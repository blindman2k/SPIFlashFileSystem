
#require "bullwinkle.class.nut:2.0.1"

bull <- Bullwinkle();

bull.on("http.get", function(message, reply) {
	// Perform the download
	local request = message.data;
	local from = request.offset;
	local to = request.offset + request.length - 1
	local headers = { Range = format("bytes=%u-%u", from, to) };

	server.log("Requesting " + from + "-" + to + " from " + request.url);
	http.get(request.url, headers).sendasync(function(resp) {
	    if (resp.statuscode < 300) {
	        // Success
	        reply(resp.body);
	    } else if (resp.statuscode == 416) {
	        // No more data in that range
	        reply(null)
	    } else {
	        // Error
	        server.log("Response code: " + resp.statuscode);
	        reply(false);
	    }
	});

});