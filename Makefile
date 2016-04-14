agdajs:
	agda --js ./LambdaMaps.agda
	gsed -i  "1i if (typeof define !== 'function') { var define = require('amdefine')(module) }" jAgda.*.js

clean:
	rm -f *.agdai jAgda.*.js
