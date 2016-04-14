agdajs:
	agda --js ./LambdaMaps.agda
        # I had to brew install gnu-sed to get gsed on a mac,
        # if you're on a more sensible unix, you can probably just get away with "sed":
	gsed -i  "1i if (typeof define !== 'function') { var define = require('amdefine')(module) }" jAgda.*.js

clean:
	rm -f *.agdai jAgda.*.js
