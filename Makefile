agdajs:
	agda --js ./LambdaMaps.agda
	perl post-process.pl

# $ node
# > x = require('./LambdaMaps-agda')

clean:
	rm -f *.agdai jAgda.*.js LambdaMaps-agda.js
