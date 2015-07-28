// Copyright (c) 2015 Electric Imp
// This file is licensed under the MIT License
// http://opensource.org/licenses/MIT

const SPIFLASHFILESYSTEM_BLOCK_SIZE = 65536;
const SPIFLASHFILESYSTEM_SECTOR_SIZE = 4096;
const SPIFLASHFILESYSTEM_PAGE_SIZE = 256;
const SPIFLASHFILESYSTEM_PAGES_PER_SECTOR = 16;
const SPIFLASHFILESYSTEM_PAGES_PER_BLOCK = 256;
const SPIFLASHFILESYSTEM_SECTORS_PER_BLOCK = 16;

const SPIFLASHFILESYSTEM_HEADER_SIZE = 5;
const SPIFLASHFILESYSTEM_BODY_SIZE = 251; // SFFS_PAGE_SIZE - SFFS_HEADER_SIZE

const SPIFLASHFILESYSTEM_FLAGS_NEW = 0x01;
const SPIFLASHFILESYSTEM_FLAGS_USED = 0x02;
const SPIFLASHFILESYSTEM_FLAGS_DATA = 0x04;
const SPIFLASHFILESYSTEM_FLAGS_INDEX = 0x08;
const SPIFLASHFILESYSTEM_FLAGS_DELETED = 0x10;
const SPIFLASHFILESYSTEM_FLAGS_DIRTY = 0x20;
const SPIFLASHFILESYSTEM_FLAGS_APPENDED = 0x40;
const SPIFLASHFILESYSTEM_FLAGS_FREE = 0xFF;

const SPIFLASHFILESYSTEM_LOOKUP_MASK_ID = 0x7FFF;
const SPIFLASHFILESYSTEM_LOOKUP_MASK_INDEX = 0x8000;
const SPIFLASHFILESYSTEM_LOOKUP_FREE  = 0xFFFF;
const SPIFLASHFILESYSTEM_LOOKUP_ERASED  = 0x0000;

const SPIFLASHFILESYSTEM_LOOKUP_STAT_ERASED = 0x00;
const SPIFLASHFILESYSTEM_LOOKUP_STAT_INDEX  = 0x01;
const SPIFLASHFILESYSTEM_LOOKUP_STAT_DATA   = 0x02;
const SPIFLASHFILESYSTEM_LOOKUP_STAT_FREE   = 0xFF;

const SPIFLASHFILESYSTEM_FREECACHE_MINIMUM = 20;

const SPIFLASHFILESYSTEM_SPIFLASH_VERIFY = 1; // SPIFLASH_POSTVERIFY

class SPIFlashFileSystem {

    static version = [0, 1, 0];

    _serializer = null; // Reference to Serializer (or object with same interface)
    _flash = null;      // Reference to hardware.spiflash (or object with same interface)
    _size = null;       // The size of _flash
    _start = null;      // First byte allocated to fs (must be start of block)
    _end = null;        // Last byte allocated to fs (must be end of block)
    _len = null;        // The length of space allocated to file system

    _blocks = 0;        // Number of blocks in file system
    _sectors = 0;       // Numer of sectors in file system
    _pages = 0;         // Number of pages in file system

    _enables = 0;       // Counting semaphore for enables/disables
    _lastFilePtr = 0;
    _lastId = 0;

    _fat = null;
    _fatStats = null;
    _openFiles = null;

    _autoGcMaxFree = 64;
    _autoGcMinFree = 16;

    _pageCache = null;
    _freePageCache = null;

    //--------------------------------------------------------------------------
    constructor(start = null, end = null, flash = null, serializer = null) {

        // Set object references
        _flash = flash ? flash : hardware.spiflash;
        _serializer = serializer ? serializer : Serializer;

        // Get the size
        _enable();
        _size = _flash.size();
        _disable();

        // Set the start / end
        _start = start ? start : 0;
        _end = end ? end : _size;

        // Validate the start / end
        if (_start % SPIFLASHFILESYSTEM_BLOCK_SIZE != 0 || _start >= _size) throw "Invalid Boundary (start)"
        if (_end % SPIFLASHFILESYSTEM_BLOCK_SIZE != 0 || _end <= _start) throw "Invalid Boundary (end)";

        // Initiate filesystem properties
        _fat = {};
        _openFiles = {};
        _pageCache = {};
        _freePageCache = [];

        // Calculate size properties
        _len = _end - _start;
        _blocks = _len / SPIFLASHFILESYSTEM_BLOCK_SIZE;
        _sectors = _len / SPIFLASHFILESYSTEM_SECTOR_SIZE;
        _pages = _len / SPIFLASHFILESYSTEM_PAGE_SIZE;

        _fatStats = { lookup = 0, free = 0, used = 0, erased = 0 };
    }

    //--------------------------------------------------------------------------
    function init(callback = null) {

        if (_openFiles.len() > 0) return server.error("Can't call init() with open files");

        // Scan the object lookup tables for files
        _fat = {};
        _openFiles = {};
        _pageCache = {};
        _freePageCache = [];

        _fatStats = _scan(function(file) {
            // server.log(Utils.logObj(file));
            assert(file != null && file.fname != null);
            _fat[file.fname] <- file;
            if (file.id > _lastId) _lastId = file.id;
            if (callback) callback(file);
        }.bindenv(this))

        // server.log("FAT stats: " + Utils.logObj(_fatStats))

    }


    //--------------------------------------------------------------------------
    function dimensions() {
        return { "size": _size, "len": _len, "start": _start, "end": _end }
    }


    //--------------------------------------------------------------------------
    function eraseFile(fname) {
        if (!(fname in _fat)) throw "Can't find file '" + fname + "' to erase";
        foreach (ptr,file in _openFiles) {
            if (file == _fat[fname]) throw "Can't erase open file '" + fname + "'";
        }

        // server.log("Erasing " + fname)
        local file = _fat[fname];
        local zeros = blob(SPIFLASHFILESYSTEM_HEADER_SIZE);

        _enable();

        // Scan for the pages for this file
        local scan = _getFilePages(file);

        // Zero out the data pages
        foreach (page,span in scan.psDat) {
            // server.log("+ Data @ " + page);
            local res = _flash.write(page, zeros, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
            assert(res == 0);

            // Update the stats
            _fatStats.erased++;
            _fatStats.used--;
        }

        // Zero out the index pages
        foreach (page,span in scan.psIdx) {
            // server.log("+ Index @ " + page);
            local res = _flash.write(page, zeros, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
            assert(res == 0);

            // Update the stats
            _fatStats.erased++;
            _fatStats.used--;
        }

        // Zero out the lookup pages in any block that matches the file id
        for (local b = 0; b < _blocks; b++) {

            // Read the first two pages
            local block = _start + (b * SPIFLASHFILESYSTEM_BLOCK_SIZE);
            local lookupData = _flash.read(block, 2*SPIFLASHFILESYSTEM_PAGE_SIZE);

            local lookupDataChanged = false;
            lookupData.seek(2 * SPIFLASHFILESYSTEM_PAGES_PER_SECTOR); // Skip past the first sector
            while (!lookupData.eos()) {

                // Read the next page
                local objData = lookupData.readn('w');
                local id = (objData & SPIFLASHFILESYSTEM_LOOKUP_MASK_ID);
                if (id == file.id) {

                    // We have a matching id, so go back over it with 0's
                    lookupData.seek(-2, 'c');
                    lookupData.writen(0x0000, 'w');
                    lookupDataChanged = true;
                }

            }

            // Now write the lookup table back
            if (lookupDataChanged) {
                lookupData.seek(0);
                local res = _flash.write(block, lookupData, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
                assert(res == 0);
            }
        }

        _disable();

        // Update the fat
        delete _fat[fname];
    }


    //--------------------------------------------------------------------------
    function eraseAll() {

        if (_openFiles.len() > 0) return server.error("Can't call eraseAll() with open files");

        // Format all the sectors
        _enable()
        for (local i = 0; i < _sectors; i++) {
            _flash.erasesector(i * SPIFLASHFILESYSTEM_SECTOR_SIZE);
        }
        _disable()
        imp.sleep(0.05);

        // Close all open files and empty the FAT
        _fat = {};
        _openFiles = {};
        _pageCache = {};
        _freePageCache = [];
        _fatStats = { lookup = _blocks*SPIFLASHFILESYSTEM_PAGES_PER_SECTOR,
                      free   = _blocks*(SPIFLASHFILESYSTEM_PAGES_PER_BLOCK - SPIFLASHFILESYSTEM_PAGES_PER_SECTOR),
                      used = 0,
                      erased = 0 };

        _lastFilePtr = 0;
        _lastId = 0;

        server.log("Filesystem erased");
    }


    //--------------------------------------------------------------------------
    function fileExists(fname) {
        return (fname in _fat);
    }


    //--------------------------------------------------------------------------
    function info(fname) {

        if (typeof fname == "integer") {
            // We have a file pointer
            local fileptr = fname;
            return _openFiles[fileptr];
        } else if (typeof fileptr == "string") {
            // We have a file name
            if (!(fname in _fat)) {
                throw "Can't find '" + fname + "' info.";
            }
            return _fat[fname];
        }
    }


    //--------------------------------------------------------------------------
    function size(fileptr) {
        return info(fileptr).size;
    }


    //--------------------------------------------------------------------------
    function open(fname, mode) {
        // Check the mode
        if ((mode == "r") && !(fname in _fat)) {
            throw "Can't open '" + fname + "' for reading, not found.";
        } else if ((mode == "w") && (fname in _fat)) {
            throw "Can't open '" + fname + "' for writing, already exists.";
        } else if (mode != "r" && mode != "w" && mode != "a") {
            throw "Unknown mode: " + mode;
        } else

        // Create a new file pointer from the FAT or a new file
        _lastFilePtr++;
        if (fname in _fat) {
            // This is an existing file, so just point to the same FAT entry
            _openFiles[_lastFilePtr] <- _fat[fname];
        } else {
            // Create a new open file entry for this file but not a FAT entry
            _lastId = (_lastId + 1) % SPIFLASHFILESYSTEM_LOOKUP_MASK_ID;
            // NOTE: We really should check if _lastId already exists in the file system
            _openFiles[_lastFilePtr] <- {
                id = ++_lastId,
                fname = fname,
                flags = SPIFLASHFILESYSTEM_FLAGS_NEW,
                size = 0,
                lsDat = 0,
                lsIdx = 0,
                pgNxt = null,
                pgsIdx = blob(),
                pgsDat = blob()
            };
        }

        // Return a new file object
        return SPIFlashFileSystem.File(this, _lastFilePtr, fname, mode);
    }


    //--------------------------------------------------------------------------
    function gc(initCallback = null) {

        if (_openFiles.len() > 0) return server.error("Can't call gc() with open files");

        _enable();

        // Scan the storage collecting garbage stats
        local scan = _gc_scan();

        // Move all the used pages away from the erased pages
        for (local s = 0; s < _sectors; s++) {

            // Does this sector have anything to collect
            if (scan.erased[s] > 0 && scan.used[s] <= scan.stats.free) {

                local sector = s * SPIFLASHFILESYSTEM_SECTOR_SIZE;
                local block = _getBlockFromAddr(sector);

                if (scan.erased[s] > 0) {

                    // We may have stuff to move
                    // server.log(format("Moving %d pages from sector %d to recover %d erased pages", scan.used[s], s, scan.erased[s]))

                }

                if (scan.used[s] > 0) {

                    // Read the lookup data
                    local lookupData = _readLookupPage(block, true);

                    // Grab the free pages from another sector
                    local freePages = _nextFreePage(scan.used[s], sector);
                    // server.log(format("Requested %d free pages and got %d", stats.used[s], freePages.len()))

                    // Skip straight to the sector's lookup
                    for (local i = 0; i < lookupData.count && scan.used[s] > 0; i++) {

                        local lookup = _getLookupData(lookupData, i);

                        // This is not from the sector we are looking at
                        if (_getSectorFromAddr(lookup.page) != sector) {
                            continue;
                        }

                        // server.log("Data for lookup of page " + lookup.page + " sector " + sector + " in block " + block + " stat " + lookup.stat);

                        // These aren't interesting pages
                        if (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_FREE) {
                            // server.log(format("- Skipping empty page %d", lookup.page))
                            continue;
                        } else if (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_ERASED) {
                            // server.log(format("- Skipping erased page %d", lookup.page))
                            continue;
                        }

                        // Pop a free page off the list
                        local freePage = freePages[0];
                        freePages.remove(0);

                        local s_free = _getSectorFromAddr(freePage) / SPIFLASHFILESYSTEM_SECTOR_SIZE;
                        local s_lookup = _getSectorFromAddr(lookup.page) / SPIFLASHFILESYSTEM_SECTOR_SIZE;

                        // Read the next page and if it is "used" then move it
                        if (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_INDEX) {

                            // server.log(format("+ Moving %s page %02x (sector %02x) to %02x (sector %02x)",  "index", lookup.page, s_lookup, freePage, s_free))

                            // Copy the data over
                            _copyPage(lookup.page, freePage, lookup);

                            // Finally, erase the original page
                            _erasePage(lookup.page);

                        } else if (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_DATA) {

                            // server.log(format("+ Moving %s page %02x (sector %02x) to %02x (sector %02x)", "data", lookup.page, s_lookup, freePage, s_free))

                            // Copy the data over
                            _copyPage(lookup.page, freePage, lookup);

                            // Finally, erase the original page
                            _erasePage(lookup.page);

                        } else {
                            continue;
                        }


                        // Adjust the sector counts
                        scan.used[s_free]++;
                        scan.used[s_lookup]--;
                        scan.erased[s_lookup]++;
                        scan.stats.erased++;
                        scan.stats.free--;

                    }
                }

                // Now we can erase the sector and correct the lookup table
                if (scan.used[s] == 0 && scan.erased[s] > 0) {

                    // server.log(format("+ Erasing sector %d (data at page %02x, lookup at page %02x)", s, sector, block));

                    // Read in the old lookup table and erase the sector from it
                    local lookupData = _flash.read(block, 2 * SPIFLASHFILESYSTEM_PAGE_SIZE);
                    local start = 2 * (sector - block) / SPIFLASHFILESYSTEM_PAGE_SIZE;

                    lookupData.seek(start);
                    for (local i = 0; i < SPIFLASHFILESYSTEM_PAGES_PER_SECTOR; i++) {
                        lookupData.writen(SPIFLASHFILESYSTEM_LOOKUP_FREE, 'w');
                    }

                    // Rewrite the lookup table
                    _flash.erasesector(block); imp.sleep(0.05);
                    lookupData.seek(0);
                    local res = _flash.write(block, lookupData, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
                    assert(res == 0);

                    // Perform the erase of the data sector
                    _flash.erasesector(sector); imp.sleep(0.05);

                    // Update the stats
                    scan.free[s] += scan.used[s] + scan.erased[s];
                    scan.used[s] = 0;
                    scan.erased[s] = 0;

                } else {

                    // server.log(format("+ NOT Erasing sector %d because used %d erased %d", s, scan.used[s], scan.erased[s]));

                }
            }
        }

        _disable();

        // Rescan the result
        _fatStats = _gc_scan();

        // Reinitialise the file system
        init(initCallback);

    }


    //--------------------------------------------------------------------------
    function repair(initCallback = null) {

        if (_openFiles.len() > 0) return server.error("Can't call repair() with open files");

        _enable();

        // Repair the lookup tables by reading the contents of every page
        local lookupData = blob(2 * SPIFLASHFILESYSTEM_PAGE_SIZE);
        local lookupWord;
        for (local b = 0; b < _blocks; b++) {

            //
            local block = _start + (b * SPIFLASHFILESYSTEM_BLOCK_SIZE);
            lookupData.seek(0);

            // Read the pages
            for (local p = 0; p < SPIFLASHFILESYSTEM_PAGES_PER_BLOCK; p++) {

                local page = block + (p * SPIFLASHFILESYSTEM_PAGE_SIZE);
                if (page < block + SPIFLASHFILESYSTEM_SECTOR_SIZE) {

                    // server.log("SKIP: " + block + ", " + page)

                    // This is from the first sector, which is lookup data
                    lookupWord = SPIFLASHFILESYSTEM_LOOKUP_ERASED;

                } else {

                    // server.log("KEEP: " + block + ", " + page)

                    // This is a data or index page
                    local data = _readDataPage(page);

                    if ((data.flags & SPIFLASHFILESYSTEM_FLAGS_INDEX) == SPIFLASHFILESYSTEM_FLAGS_INDEX) {
                        // This page has an index
                        lookupWord = data.id | SPIFLASHFILESYSTEM_LOOKUP_MASK_INDEX;
                    } else if ((data.flags & SPIFLASHFILESYSTEM_FLAGS_DATA) == SPIFLASHFILESYSTEM_FLAGS_DATA) {
                        // This page has data
                        lookupWord = data.id;
                    } else if (data.flags == SPIFLASHFILESYSTEM_FLAGS_FREE) {
                        // This page is free
                        lookupWord = SPIFLASHFILESYSTEM_LOOKUP_FREE;
                    } else {
                        // This page is deleted
                        lookupWord = SPIFLASHFILESYSTEM_LOOKUP_ERASED;
                    }
                }

                // Add the word to the lookup data
                lookupData.writen(lookupWord, 'w')

            }

            // Now erase and rewrite the lookup table
            // server.log("Repairing block " + b)
            _flash.erasesector(block); imp.sleep(0.05);
            lookupData.seek(0);
            local res = _flash.write(block, lookupData, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
            assert(res == 0);
        }

        _disable();

        // Now reinitialise the FAT
        init(initCallback);

    }


    //--------------------------------------------------------------------------
    function setAutoGc(maxPages, minPages = null) {

        // Override the default auto garbage collection settings
        if (maxPages != null) _autoGcMaxFree = maxPages;
        if (minPages != null) _autoGcMinFree = minPages;

    }


    //--------------------------------------------------------------------------
    function _autoGc() {

        // Is it worth gc'ing? If so, start it.
        if (_openFiles.len() == 0
         && _fatStats.free > 0
         && _fatStats.free <= _autoGcMaxFree
         && _fatStats.free >= _autoGcMinFree
         && _fatStats.erased > 0) {
            server.log("Automatically starting garbage collection");
            gc();
        }

    }


    //--------------------------------------------------------------------------
    function _close(fileptr) {

        // If the file has changed, write the final results to the filesystem
        local file = _openFiles[fileptr];
        local scan = null;
        local psIdx = null;
        local psDat = null;

        if (file.flags & (SPIFLASHFILESYSTEM_FLAGS_DIRTY | SPIFLASHFILESYSTEM_FLAGS_APPENDED)) {
            // Scan for all the pages used by this file
            scan = _getFilePages(file);
            psIdx = _sortTableByValues(scan.psIdx);
            psDat = _sortTableByValues(scan.psDat);
        }

        // If we have an appended file then we have to remove the old index header to update the size
        if (file.flags & SPIFLASHFILESYSTEM_FLAGS_APPENDED && psIdx.len() > 0) {

            _erasePage(psIdx[0]);

            psIdx[0] = _nextFreePage();

            // Update the cache too
            if (file.id in _pageCache) {
                _pageCache[file.id].psIdx[0] <- psIdx[0];
            }

            // Update the stats
            _fatStats.erased++;
            _fatStats.free--;

        }

        // Check if the file has been changed
        if (file.flags & SPIFLASHFILESYSTEM_FLAGS_DIRTY) {

            // Remove the dirty flag and add the used flag
            file.flags = file.flags ^ SPIFLASHFILESYSTEM_FLAGS_DIRTY;
            file.flags = file.flags | SPIFLASHFILESYSTEM_FLAGS_USED;

            // server.log(format("Closing '%s' which is now %d bytes\n\n", _openFiles[fileptr].fname, _openFiles[fileptr].size));

            // Write all the indices
            local span = 0;
            while (psDat.len() > 0) {

                // Use an existing index or make a new one
                local index = null;
                if (psIdx.len() > 0) {

                    // Use an existing index
                    index = psIdx[0];
                    psIdx.remove(0);

                } else {

                    // Make a new index
                    index = _nextFreePage();

                    // Add it to the cache if required
                    if (file.id in _pageCache) {
                        _pageCache[file.id].psIdx[span] <- index;
                    }

                    // Update the stats
                    _fatStats.used++;
                    _fatStats.free--;
                }

                // Now write the index, possible over the previous one.
                _writeIndexPage(file, index, psDat, span++);
            }

        }

        // Now drop the file pointer;
        delete _openFiles[fileptr];

        // Auto garbage collect if required
        _autoGc()
    }


    //--------------------------------------------------------------------------
    function _read(fileptr, ptr, len = null) {

        // Check the length is valid
        local file = _openFiles[fileptr];
        if (len == null) len = file.size;
        local size = file.size;
        if (ptr + len >= size) len = size - ptr;
        if (len <= 0) return blob();

        // Now read the data
        local data = blob();
        local rem_total = len;
        local page_no = ptr / SPIFLASHFILESYSTEM_BODY_SIZE;
        local page_offset = ptr % SPIFLASHFILESYSTEM_BODY_SIZE;
        local togo = ptr;

        // server.log("Reading: " + ptr + " (page " + page_no + ", offset " + page_offset + ") from " + file.psDat.len() + " psDat and " + file.psIdx.len() + " psIdx");
        // Scan for the pages for this file
        local scan = _getFilePages(file);
        local psDat = _sortTableByValues(scan.psDat);

        _enable();
        foreach (page in psDat) {
            // Shuffle to the right page
            if (togo <= SPIFLASHFILESYSTEM_BODY_SIZE) {

                // Read till the end of the page at most
                local rem_in_page = SPIFLASHFILESYSTEM_BODY_SIZE - page_offset;
                local rem = (rem_total > rem_in_page) ? rem_in_page : rem_total;
                _flash.readintoblob(page + SPIFLASHFILESYSTEM_HEADER_SIZE + page_offset, data, rem);
                // server.log("Reading from: " + (page + SPIFLASHFILESYSTEM_HEADER_SIZE + page_offset) + " in span " + file.psDat[page]);

                // Reload for next page
                page_offset = 0;
                rem_total -= rem;
                if (rem_total == 0) break;
            }
            togo -= SPIFLASHFILESYSTEM_BODY_SIZE;
        }
        _disable();

        data.seek(0);
        return data;
    }


    //--------------------------------------------------------------------------
    function _readLookupPage(block, withRaw = false) {

        // Read the first two page (the lookup table)
        _enable();
        local lookupData = _flash.read(block, 2 * SPIFLASHFILESYSTEM_PAGE_SIZE).tostring();
        _disable();

        // Calculate the page we're on
        local page = block + SPIFLASHFILESYSTEM_SECTOR_SIZE;

        // Store this data as local variables until we're ready to return to
        // save time indexing into a table
        local count = 0, ids = [], stats = [], pages = [], addrs = [], raws = [];

        // Skip past the first 2x16 bytes, which are the lookup pages (the whole first sector)
        local start = 2 * SPIFLASHFILESYSTEM_PAGES_PER_SECTOR;
        local end = (2 * SPIFLASHFILESYSTEM_PAGE_SIZE);

        for(local i = start; i < end; i+= 2) {
            // Grab the current data
            local objData = (lookupData[i] << 8) + lookupData[i+1];

            count++;
            pages.push(page);
            addrs.push(block+i);

            ids.push(objData & SPIFLASHFILESYSTEM_LOOKUP_MASK_ID);
            if (withRaw) raws.push(objData);

            if (objData == SPIFLASHFILESYSTEM_LOOKUP_FREE) {
                stats.push(SPIFLASHFILESYSTEM_LOOKUP_STAT_FREE);
            } else if (objData == SPIFLASHFILESYSTEM_LOOKUP_ERASED) {
                stats.push(SPIFLASHFILESYSTEM_LOOKUP_STAT_ERASED);
            } else if ((objData & SPIFLASHFILESYSTEM_LOOKUP_MASK_INDEX) == SPIFLASHFILESYSTEM_LOOKUP_MASK_INDEX) {
                stats.push(SPIFLASHFILESYSTEM_LOOKUP_STAT_INDEX);
            } else {
                stats.push(SPIFLASHFILESYSTEM_LOOKUP_STAT_DATA);
            }

            // Move forward
            page += SPIFLASHFILESYSTEM_PAGE_SIZE;
        }
        // Build table to return
        return { "count": count, "id": ids, "stat": stats, "page": pages, "addr": addrs, "raw": raws };
    }



    //--------------------------------------------------------------------------
    function _getLookupData(lookupPages, i) {
        local lookup = {};
        lookup.id <- lookupPages.id[i];
        lookup.stat <- lookupPages.stat[i];
        lookup.page <- lookupPages.page[i];
        lookup.addr <- lookupPages.addr[i];
        if (lookupPages.raw.len() > 0) lookup.raw <- lookupPages.raw[i];
        return lookup;
    }


    //--------------------------------------------------------------------------
    function _readIndexPage(indexPage, withRaw = false) {
        _enable();

        // Read the index page and parse the header
        local indexData = _flash.read(indexPage, SPIFLASHFILESYSTEM_PAGE_SIZE);
        local str = indexData.tostring();
        local i = 0;

        local index = {};

        // index.flags <- indexData.readn('b');
        index.flags <- str[i++];

        // index.id <- indexData.readn('w');       // This should match the previous id
        index.id <- (str[i+1]<<8) + str[i];
        i+=2;

        // index.span <- indexData.readn('w');
        index.span <- (str[i+1]<<8) + str[i];
        i+=2;

        if (index.span == 0) {
            // index.size <- indexData.readn('i');
            index.size <- (str[i+3]<<24) + (str[i+2]<<16) + (str[i+1]<<8) + str[i]
            i+=4;

            // local fnameLen = indexData.readn('b');
            local fnameLen = str[i++];

            // index.fname <- indexData.readstring(fnameLen);
            index.fname <- str.slice(i, i+fnameLen);
            i += fnameLen
        }
        // index.header <- indexData.tell();
        index.header <- i;

        if (withRaw) index.raw <- indexData;

        // Read the page numbers if there are any left
        // NOTE: This is a very slow operation and would be much faster if it was left as a blob.
        //       But this takes lots of hard changes elsewhere.
        index.dataPages <- [];

        // Current position
        local leftToRead = SPIFLASHFILESYSTEM_PAGE_SIZE - index.header;

        while (leftToRead >= 2) {
            // local dataIdx = indexData.readn('w');
            local dataIdx = (str[i+1]<<8)+str[i];
            i+=2;

            leftToRead -= 2;

            if (dataIdx != SPIFLASHFILESYSTEM_LOOKUP_ERASED && dataIdx != SPIFLASHFILESYSTEM_LOOKUP_FREE) {
                index.dataPages.push(dataIdx * SPIFLASHFILESYSTEM_PAGE_SIZE);
                // server.log(format("* Found dataPage %02x on index %02x for id %d", (dataPageOffset * SPIFLASHFILESYSTEM_PAGE_SIZE), indexPage, index.id))
            }
        }
        _disable();

        return index;
    }

    //--------------------------------------------------------------------------
    function _readPageHeader(page) {

        assert(page < _end);

        _enable();

        // Read the header
        local headerBlob = _flash.read(page, SPIFLASHFILESYSTEM_HEADER_SIZE+5);

        // Parse the header
        local headerData = {};
        headerData.flags <- headerBlob.readn('b');
        headerData.id <- headerBlob.readn('w');
        headerData.span <- headerBlob.readn('w');

        if (headerData.flags == SPIFLASHFILESYSTEM_FLAGS_FREE) {

            // This page is free
            headerData.type <- SPIFLASHFILESYSTEM_LOOKUP_STAT_FREE;

        } else if (headerData.flags & SPIFLASHFILESYSTEM_FLAGS_INDEX) {

            // This page is an index
            headerData.type <- SPIFLASHFILESYSTEM_LOOKUP_STAT_INDEX;
            if (headerData.span == 0) {
                // This page is a index header specifically
                headerData.size <- headerBlob.readn('i');
                local fnameLen = headerBlob.readn('b');
                headerData.fname <- _flash.read(page+SPIFLASHFILESYSTEM_HEADER_SIZE+5, fnameLen).tostring();
            }

        } else if (headerData.flags & SPIFLASHFILESYSTEM_FLAGS_DATA) {

            // This page has data
            headerData.type <- SPIFLASHFILESYSTEM_LOOKUP_STAT_DATA;

        } else {

            // This page is deleted
            headerData.type <- SPIFLASHFILESYSTEM_LOOKUP_STAT_ERASED;

        }

        _disable();
        return headerData;
    }


    //--------------------------------------------------------------------------
    function _readDataPage(dataPage, withData = false) {

        assert(dataPage < _end);

        _enable();

        local dataBlob = _flash.read(dataPage, withData ? SPIFLASHFILESYSTEM_PAGE_SIZE : SPIFLASHFILESYSTEM_HEADER_SIZE);

        // Parse the header
        local data = {};
        data.flags <- dataBlob.readn('b');
        data.id <- dataBlob.readn('w');
        data.span <- dataBlob.readn('w');

        if (withData) {
            data.data <- dataBlob.readblob(SPIFLASHFILESYSTEM_PAGE_SIZE - 5);
        }

        _disable();
        return data;
    }


    //--------------------------------------------------------------------------
    function _write(fileptr, data) {

        // Make sure we have a blob
        if (typeof data == "string") {
            local data_t = blob(data.len());
            data_t.writestring(data);
            data = data_t;
            data.seek(0);
        } else if (typeof data != "blob") {
            throw "Can only write blobs and strings";
        }
        // server.log(format("Writing to '%s' for %d bytes", _openFiles[fileptr].fname, data.len()));

        local bytesWritten = 0;
        local file = _openFiles[fileptr];

        // Make sure the open file and the FAT match. This is only relevant when its a new file
        _fat[file.fname] <- file;

        _enable();

        // Make sure we have an index
        if (file.lsIdx == 0) {

            // Make sure we never come back here again
            file.lsIdx++;

            // Create a new index header page
            local index = _nextFreePage();

            // Add it to the cache if required
            if (file.id in _pageCache) {
                _pageCache[file.id].psIdx[0] <- index;
            }

            _writeIndexPage(file, index);

            // Update the stats
            _fatStats.used++;
            _fatStats.free--;

        }

        // Now write all the data
        local pagesRequired = math.ceil(1.0 * data.len() / SPIFLASHFILESYSTEM_BODY_SIZE).tointeger();
        local freePages =  _nextFreePage(pagesRequired);
        while (!data.eos()) {

            // Find the next write location
            if (file.size % SPIFLASHFILESYSTEM_BODY_SIZE == 0) {

                file.lsDat++;

                // Just in case we have run out, get another page
                if (freePages.len() == 0) freePages =  _nextFreePage(1);
                file.pgNxt = freePages[0];
                freePages.remove(0);
                // server.log("New page, span " + file.lsDat + " at " + file.pgNxt);

                // Add it to the cache if required
                if (file.id in _pageCache) {
                    _pageCache[file.id].psDat[file.lsDat] <- file.pgNxt;
                }

                // Update the stats
                _fatStats.erased++;
                _fatStats.free--;

            } else {
                // server.log("Same page, span " + file.lsDat + " at " + file.pgNxt);
            }

            // Write the data to the free page
            local bytes = _writeDataPage(file, data, file.pgNxt, file.lsDat);
            bytesWritten += bytes;
            file.size += bytes;
            // server.log("+- " + bytes + " bytes")

            // Add the dirty flag and appended flag
            file.flags = file.flags | SPIFLASHFILESYSTEM_FLAGS_DIRTY;
            if (file.flags & SPIFLASHFILESYSTEM_FLAGS_USED) {
                file.flags = file.flags | SPIFLASHFILESYSTEM_FLAGS_APPENDED;
            }

        }

        _disable();

        return bytesWritten;
    }


    //--------------------------------------------------------------------------
    function _writeIndexPage(file, indexPage, dataPages = null, span = 0) {
        _enable();

        local block = _getBlockFromAddr(indexPage);
        // server.log(format("- Writing index span %d for id %d at %d in block %d", span, file.id, indexPage, block))

        // Write the new index
        local indexData = blob(SPIFLASHFILESYSTEM_HEADER_SIZE);
        indexData.writen(SPIFLASHFILESYSTEM_FLAGS_INDEX, 'b');
        indexData.writen(file.id, 'w');
        indexData.writen(span, 'w');
        // server.log("Index span " + span);

        if (span == 0) {
            // This is an index header page, so contains some extra info
            if (file.flags & SPIFLASHFILESYSTEM_FLAGS_NEW) {
                // We dont know the final size yet
                indexData.writen(0xFFFFFFFF, 'i');
                file.flags = file.flags ^ SPIFLASHFILESYSTEM_FLAGS_NEW;
            } else {
                indexData.writen(file.size, 'i');
            }
            indexData.writen(file.fname.len(), 'b');
            indexData.writestring(file.fname);
        }

        // Append the list of pages, until the end of the page
        if (dataPages != null) {
            while (dataPages.len() > 0 && indexData.len() < 255) {
                // Add the page number of this page to the index
                local dataPage = dataPages[0];
                local dataPageNumber = dataPage / SPIFLASHFILESYSTEM_PAGE_SIZE;
                indexData.writen(dataPageNumber, 'w');
                // server.log(format("* Wrote dataPage %02x on index %02x for id %d", dataPage, indexPage, file.id))

                // Shift the first page off
                dataPages.remove(0);
            }
        }
        local res = _flash.write(indexPage, indexData, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);

        // server.log("Writing index span " + span + ", for filename " + file.fname + " at " + indexPage);

        // Update the object lookup table to indicate this is an index of this particular file id
        local lookup = block + (2 * (indexPage - block) / SPIFLASHFILESYSTEM_PAGE_SIZE);
        local lookupData = blob(2);
        lookupData.writen(file.id | SPIFLASHFILESYSTEM_LOOKUP_MASK_INDEX, 'w');
        local res = _flash.write(lookup, lookupData, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);

        // Update the FAT
        if ("pgsIdx" in file) {
            _addPageToCache(indexPage, file.pgsIdx);
        } else {
            // We don't know which file this belongs to. This should only happen inside gc() so it should be safe to ignore.
        }

        // Track the last index span
        if ("lsIdx" in file && span > file.lsIdx) file.lsIdx = span;

        _disable();
    }


    //--------------------------------------------------------------------------
    function _writeDataPage(file, data, page, span) {
        _enable();

        local pageOffset = file.size % SPIFLASHFILESYSTEM_BODY_SIZE;
        local block = _getBlockFromAddr(page);

        // server.log(format("- Writing data span %d for id %d at %d in block %d", span, file.id, page, block))

        // Write the page header
        local header = blob(SPIFLASHFILESYSTEM_HEADER_SIZE);
        header.writen(SPIFLASHFILESYSTEM_FLAGS_DATA, 'b');
        header.writen(file.id, 'w');
        header.writen(span, 'w');
        local res = _flash.write(page, header, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);
        // server.log(format("+ Writing data header at %d for %d bytes (span %d)", page, header.len(), span))

        // Write the page data
        local ptr = page + SPIFLASHFILESYSTEM_HEADER_SIZE + pageOffset;
        local rem_in_page = SPIFLASHFILESYSTEM_BODY_SIZE - pageOffset;
        local rem_in_data = data.len() - data.tell();
        local bytes = (rem_in_page < rem_in_data) ? rem_in_page : rem_in_data;
        local res = _flash.write(ptr, data.readblob(bytes), SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);
        // server.log(format("+ Writing data at %d for %d bytes", ptr, bytes))

        // Update the object lookup table
        local lookup = block + (2 * (page - block) / SPIFLASHFILESYSTEM_PAGE_SIZE);
        local data = blob(1);
        data.writen(file.id, 'w');
        local res = _flash.write(lookup, data, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);
        // server.log(format("= Writing data lookup at %d to 0x%04x\n\n", lookup, file.id))

        // Update the FAT
        if ("pgsDat" in file) {
            _addPageToCache(page, file.pgsDat);
        } else {
            // We don't know which file this belongs to. This should only happen inside gc() so it should be safe to ignore.
        }

        _disable();

        // Let the caller know how many bytes where transfered out of the data
        return bytes;

    }


    //--------------------------------------------------------------------------
    function _addPageToCache(page, cache) {

        // Check if it is already in the page cache
        local page = page / SPIFLASHFILESYSTEM_PAGE_SIZE;
        cache.seek(0);
        while (!cache.eos()) {
            if (page == cache.readn('w')) {
                return;
            }
        }

        // It wasn't in the cache so add it
        cache.seek(0, 'e');
        cache.writen(page, 'w');

    }


    //--------------------------------------------------------------------------
    function _erasePage(page) {

        local block = _getBlockFromAddr(page);
        local zeros = blob(SPIFLASHFILESYSTEM_HEADER_SIZE);

        // server.log(format("- Erasing page %d in block %d", page, block))

        _enable();

        // Zero out the index page
        local res = _flash.write(page, zeros, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);

        // Update the object lookup table to indicate this page is erased
        local lookup = block + (2 * (page - block) / SPIFLASHFILESYSTEM_PAGE_SIZE);
        local lookupData = blob(2);
        lookupData.writen(0x0000, 'w');
        local res = _flash.write(lookup, lookupData, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);

        // Update the FAT
        _updateFilePages(page);

        _disable();
    }


    //--------------------------------------------------------------------------
    function _copyPage(srcPage, dstPage, lookup) {
        _enable();

        // Update the existing pages for this file
        local srcPageIndex = srcPage / SPIFLASHFILESYSTEM_PAGE_SIZE;
        local dstPageIndex = dstPage / SPIFLASHFILESYSTEM_PAGE_SIZE;
        local scan = (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_INDEX) ? null : _getFilePages(null, lookup.id);

        // Write the original data over the free space
        local srcData = _flash.read(srcPage, SPIFLASHFILESYSTEM_PAGE_SIZE);
        local res = _flash.write(dstPage, srcData, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);

        // Update the object lookup table for the destination
        local block = _getBlockFromAddr(dstPage);
        local lookupIndex = 2 * (dstPage - block) / SPIFLASHFILESYSTEM_PAGE_SIZE;
        local lookupUpdate = blob(2);
        lookupUpdate.writen(lookup.raw, 'w');
        local res = _flash.write(block + lookupIndex, lookupUpdate, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
        assert(res == 0);

        // Update the FAT
        _updateFilePages(srcPage, dstPage);

        // If this is a data page then update the index page list
        if (lookup.stat != SPIFLASHFILESYSTEM_LOOKUP_STAT_INDEX) {

            // Look through each of the indices for the page reference
            local last_span = 0;
            local psIdx = _sortTableByValues(scan.psIdx);
            local indexErased = false, indexAdded = false;
            foreach (indexPage in psIdx) {

                // Read the index page
                local indexUpdated = false;
                local index = _readIndexPage(indexPage, true);
                last_span = index.span;

                // Check if the source page is in this index
                local locationOfSrc = index.dataPages.find(srcPage);
                if (locationOfSrc != null) {

                    index.raw.seek(index.header);
                    while (index.raw.len() - index.raw.tell() >= 2) {
                        local pageIndex = index.raw.readn('w');
                        if (indexAdded == false && pageIndex == SPIFLASHFILESYSTEM_LOOKUP_FREE) {

                            // Write the new entry over the previous one
                            // server.log("+ Found free spot for new pageData page")
                            index.raw.seek(-2, 'c');
                            index.raw.writen(dstPageIndex, 'w');
                            indexAdded = true;
                            indexUpdated = true;

                        } else if (indexErased == false && pageIndex == srcPageIndex) {

                            // Erase the old entry
                            // server.log("+ Found and erased matching pageData page")
                            index.raw.seek(-2, 'c');
                            index.raw.writen(SPIFLASHFILESYSTEM_LOOKUP_ERASED, 'w');
                            indexErased = true;
                            indexUpdated = true;

                        }

                        // Have we finished?
                        if (indexErased && indexAdded) break;
                    }

                    // Write the updated index to disk
                    if (indexUpdated) {
                        index.raw.seek(0);
                        // server.log(format("+ Writing back index at %02x", indexPage))
                        local res = _flash.write(indexPage, index.raw, SPIFLASHFILESYSTEM_SPIFLASH_VERIFY);
                        assert(res == 0);
                    }

                    // Have we finished?
                    if (indexErased && indexAdded) break;

                }

            }

            // If we are at the end and still haven't found space so we need a new index page
            if (!indexAdded) {

                // Create a new index page
                local index = _nextFreePage();
                _writeIndexPage(lookup, index, [dstPage], last_span+1);
                // server.log(format("- Writing index span %d for id %d at %02x in block %02x", last_span+1, lookup.id, index, block))

                // Update the stats
                _fatStats.used++;
                _fatStats.free--;

            }

            // server.log("\n");
        }

        _disable();

    }


    //--------------------------------------------------------------------------
    function _getFileFromFileId(fileId) {
        foreach (fname,file in _fat) {
            if (file.id == fileId) return file;
        }
    }


    //--------------------------------------------------------------------------
    function _updateFilePages(srcPage, dstPage = 0) {

        // Convert to the word size
        local srcPage = srcPage / SPIFLASHFILESYSTEM_PAGE_SIZE;
        local dstPage = dstPage / SPIFLASHFILESYSTEM_PAGE_SIZE;
        if (srcPage == dstPage) return;

        // For each file in the fat
        foreach (fname, file in _fat) {

            // Scan through all the index pages
            file.pgsIdx.seek(0);
            while (!file.pgsIdx.eos()) {

                // Read the index
                local indexPage = file.pgsIdx.readn('w');
                if (indexPage == srcPage) {
                    file.pgsIdx.seek(-2, 'c');
                    file.pgsIdx.writen(dstPage, 'w');
                }
            }

            // Scan through all the data pages
            file.pgsDat.seek(0);
            while (!file.pgsDat.eos()) {

                // Read the index
                local dataPage = file.pgsDat.readn('w');
                if (dataPage == srcPage) {
                    file.pgsDat.seek(-2, 'c');
                    file.pgsDat.writen(dstPage, 'w');
                }
            }


        }
    }


    //--------------------------------------------------------------------------
    function _getFilePages(file, fileId = null) {

        // Normalise the parameters
        if (file == null) {
            file = _getFileFromFileId(fileId);
        } else {
            fileId = file.id;
        }

        // Check if we have the fileId in the cache
        if (fileId in _pageCache) return _pageCache[fileId];

        _enable();

        local psIdx = {}, psDat = {};

        // Scan through all the index pages
        file.pgsIdx.seek(0);
        while (!file.pgsIdx.eos()) {

            // Read the index
            local indexPage = file.pgsIdx.readn('w') * SPIFLASHFILESYSTEM_PAGE_SIZE;
            local index = _readIndexPage(indexPage);
            psIdx[indexPage] <- index.span;
        }

        // Scan through all the data pages
        file.pgsDat.seek(0);
        while (!file.pgsDat.eos()) {

            // Read the index
            local dataPage = file.pgsDat.readn('w') * SPIFLASHFILESYSTEM_PAGE_SIZE;
            local data = _readDataPage(dataPage);
            psDat[dataPage] <- data.span;
        }

        _disable();

        // Save the result in/as the cache
        if (_pageCache.len() > 4) _pageCache = {};
        _pageCache[fileId] <- { psDat=psDat, psIdx=psIdx };

        return _pageCache[fileId];

    }


    //--------------------------------------------------------------------------
    function _nextFreePage(noRequired = null, ignoreSector = null) {

        // Scan the object lookup tables for free pages
        _enable();

        local count = (noRequired == null) ? 1 : noRequired;
        local free = [];

        // Take from the cache first, unless it is ignoreing a sector
        if (ignoreSector != null) _freePageCache = [];
        while (_freePageCache.len() > 0 && free.len() < count) {
            free.push(_freePageCache[0]);
            _freePageCache.remove(0);
        }

        // Scan the object lookup tables in each blocks, starting at a random block
        if (free.len() < count) {

            local b_start = math.rand() % _blocks;
            // b_start = 0; // NOTE: Uncomment this for testing with a predictable distribution
            for (local b = 0; b < _blocks; b++) {

                local b_next = (b + b_start) % _blocks;
                local block = _start + (b_next * SPIFLASHFILESYSTEM_BLOCK_SIZE);

                // Read the lookup table
                local lookupData = _readLookupPage(block);

                // Scan through the pages starting at a random location
                local l_start = math.rand() % lookupData.count;
                // l_start = 0; // NOTE: Uncomment this for testing with a predictable distribution
                for (local i = 0; i < lookupData.count; i++) {

                    local l_next = (i + l_start) % lookupData.count;
                    local lookup = _getLookupData(lookupData, l_next);
                    if (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_FREE) {

                        local sector = _getSectorFromAddr(lookup.page);
                        if (sector != ignoreSector) {

                            // Store this page as free either for the caller or the cache
                            if (free.len() < count) {
                                // Make sure it isn't already taken from the free page cache
                                if (free.find(lookup.page) == null) {
                                    free.push(lookup.page)
                                }
                            } else {
                                _freePageCache.push(lookup.page);
                            }

                            // Do we have all we need?
                            if (free.len() == count && _freePageCache.len() >= SPIFLASHFILESYSTEM_FREECACHE_MINIMUM) break;
                        }
                    }

                }

                // Do we have all we need?
                if (free.len() == count && _freePageCache.len() >= SPIFLASHFILESYSTEM_FREECACHE_MINIMUM) break;
            }
        }

        // Now, what have we got?
        if (free.len() < count) {
            server.error(format("Requested %d pages but only found %d.", count, free.len()))
            throw "Insufficient free space, storage full";
        } else if (noRequired == null) {
            // No parameter was set, so give them the first and only item
            return free[0];
        } else {
            // Otherwise give the caller the array
            return free;
        }
    }


    //--------------------------------------------------------------------------
    function _scan(callback = null) {

        _enable();

        local mem = imp.getmemoryfree();
        local stats = { lookup = 0, free = 0, used = 0, erased = 0 };
        local files = {};

        // Scan the object lookup tables in each block, working out what is in each sector
        for (local b = 0; b < _blocks; b++) {

            local block = _start + (b * SPIFLASHFILESYSTEM_BLOCK_SIZE);
            stats.lookup += SPIFLASHFILESYSTEM_PAGES_PER_SECTOR;

            // Read all the pages except the lookup table
            for (local p = SPIFLASHFILESYSTEM_PAGES_PER_SECTOR; p < SPIFLASHFILESYSTEM_PAGES_PER_BLOCK; p++) {

                local page = block + (p * SPIFLASHFILESYSTEM_PAGE_SIZE);
                local data = _readPageHeader(page);

                // Ignore pages that are free or deleted
                if (data.type == SPIFLASHFILESYSTEM_LOOKUP_STAT_ERASED) {
                    stats.erased++;
                    continue
                } else if (data.type == SPIFLASHFILESYSTEM_LOOKUP_STAT_FREE) {
                    stats.free++;
                    continue;
                } else {
                    stats.used++;
                }

                // This is a new file, so create an entry
                local file = null;
                if (data.id in files) {
                    file = files[data.id];
                } else {
                    file = files[data.id] <- {};
                    file.id <- data.id;
                    file.flags <- SPIFLASHFILESYSTEM_FLAGS_USED;
                    file.fname <- null;
                    file.size <- 0;
                    file.lsIdx <- 0;
                    file.lsDat <- 0;
                    file.pgNxt <- 0;
                    file.pgsIdx <- blob();
                    file.pgsDat <- blob();
                }

                // Extract any data we don't already have
                if (data.type == SPIFLASHFILESYSTEM_LOOKUP_STAT_INDEX) {
                    file.pgsIdx.writen(page / SPIFLASHFILESYSTEM_PAGE_SIZE, 'w');
                    if ("fname" in data) file.fname = data.fname;
                    if ("size" in data && data.size > 0) file.size = data.size;
                    if (data.span >= file.lsIdx) {
                        file.lsIdx = data.span;
                    }
                } else if (data.type == SPIFLASHFILESYSTEM_LOOKUP_STAT_DATA) {
                    file.pgsDat.writen(page / SPIFLASHFILESYSTEM_PAGE_SIZE, 'w');
                    if (data.span >= file.lsDat) {
                        file.lsDat = data.span;
                        file.pgNxt = page;
                    }
                }

            }

        }

        _disable();

        // We have completed the scan, call the callback
        if (callback) {
            foreach (id, file in files) {
                if (callback(file) == true) {
                    break;
                }
            }
        }

        // server.log("Memory used in scan2: " + (mem - imp.getmemoryfree()))
        return stats;
    }


    //--------------------------------------------------------------------------
    function _gc_scan(print = false) {

        _enable();

        local erased = blob(_sectors);
        local free = blob(_sectors);
        local used = blob(_sectors);
        local stats = { lookup = 0, free = 0, used = 0, erased = 0 };

        // Scan the object lookup tables in each block, working out what is in each sector
        for (local b = 0; b < _blocks; b++) {

            // Read the lookup table
            local block = _start + (b * SPIFLASHFILESYSTEM_BLOCK_SIZE);
            local lookupData = _readLookupPage(block);
            local pagesErased = 0, pagesFree = 0, pagesUsed = 0;
            stats.lookup += SPIFLASHFILESYSTEM_PAGES_PER_SECTOR;

            // Skip the lookup sector in each block
            used.writen(0, 'b');
            erased.writen(0, 'b');
            free.writen(0, 'b');

            // Read the remaining
            for (local i = 0; i < lookupData.count; i++) {

                local lookup = _getLookupData(lookupData, i);
                local sector = _getSectorFromAddr(lookup.page);

                if (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_ERASED) {
                    pagesErased++;
                } else if (lookup.stat == SPIFLASHFILESYSTEM_LOOKUP_STAT_FREE) {
                    pagesFree++;
                } else {
                    pagesUsed++;
                }

                if ((lookup.page + SPIFLASHFILESYSTEM_PAGE_SIZE) % SPIFLASHFILESYSTEM_SECTOR_SIZE == 0) {

                    // The sector is over, write the counts to the blobs
                    used.writen(pagesUsed, 'b');
                    erased.writen(pagesErased, 'b');
                    free.writen(pagesFree, 'b');

                    stats.erased += pagesErased;
                    stats.free += pagesFree;
                    stats.used += pagesUsed;

                    pagesFree = pagesErased = pagesUsed = 0;
                }

            }
        }

        _disable();


        // So, whats the result?
        if (print) {
            server.log("-------[ Sector map ]-------")
            local sectors = ""; for (local i = 0; i < _sectors; i++) sectors += format("%2d ", i);
            server.log("   Sector: " + sectors);
            server.log(format("%4d %s: %s", stats.used,   "Used", Utils.logBin(used)));
            server.log(format("%4d %s: %s", stats.erased, "Ersd", Utils.logBin(erased)));
            server.log(format("%4d %s: %s", stats.free,   "Free", Utils.logBin(free)));
            server.log(format("Total space: %d / %d bytes free (%0.01f %%)",
                    stats.free * SPIFLASHFILESYSTEM_BODY_SIZE,
                    _blocks * SPIFLASHFILESYSTEM_BLOCK_SIZE,
                    100.0 * (stats.free * SPIFLASHFILESYSTEM_BODY_SIZE) / (_blocks * SPIFLASHFILESYSTEM_BLOCK_SIZE)
                    ));
            server.log("----------------------------")
        }

        return { erased = erased, free = free, used = used, stats = stats };
    }


    //--------------------------------------------------------------------------
    function _enable() {
        if (_enables++ == 0) {
            _flash.enable();
        }
    }


    //--------------------------------------------------------------------------
    function _disable() {
        if (--_enables <= 0)  {
            _enables = 0;
            _flash.disable();
        }
    }


    //--------------------------------------------------------------------------
    function _getBlockFromAddr(page) {
        return page - (page % SPIFLASHFILESYSTEM_BLOCK_SIZE);
    }


    //--------------------------------------------------------------------------
    function _getSectorFromAddr(page) {
        return page - (page % SPIFLASHFILESYSTEM_SECTOR_SIZE);
    }


    //--------------------------------------------------------------------------
    function _sortTableByValues(table) {

        // Load the table contents into an array
        local interim = [];
        foreach (k,v in table) {
            interim.push({ k = k, v = v });
        }
        // Sort the array by the key name
        interim.sort(function(first, second) {
            return first.v <=> second.v;
        });
        // Write them to a final array without the key
        local result = [];
        foreach (vv in interim) {
            result.push(vv.k);
        }
        return result;
    }


}

class SPIFlashFileSystem.File {

    _filesystem = null;
    _fileptr = null;
    _fname = null;
    _mode = null;
    _pos = 0;

    //--------------------------------------------------------------------------
    constructor(filesystem, fileptr, fname, mode) {
        _filesystem = filesystem;
        _fileptr = fileptr;
        _fname = fname;
        _mode = mode;
    }

    //--------------------------------------------------------------------------
    function close() {
        return _filesystem._close(_fileptr);
    }

    //--------------------------------------------------------------------------
    function info() {
        return _filesystem.info(_fileptr);
    }

    //--------------------------------------------------------------------------
    function seek(pos) {
        // Set the new pointer position
        _pos = pos;
        return this;
    }

    //--------------------------------------------------------------------------
    function tell() {
        return _pos;
    }

    //--------------------------------------------------------------------------
    function eof() {
        return _pos == _filesystem.size(_fileptr);
    }

    //--------------------------------------------------------------------------
    function size() {
        return _filesystem.size(_fileptr);
    }

    //--------------------------------------------------------------------------
    function read(len = null) {
        local data = _filesystem._read(_fileptr, _pos, len);
        _pos += data.len();
        return data;
    }

    //--------------------------------------------------------------------------
    function write(data) {
        if (_mode == "r") throw "Can't write - file mode is 'r'";
        local bytesWritten = _filesystem._write(_fileptr, data);
        _pos += bytesWritten;
        return bytesWritten;
    }
}
