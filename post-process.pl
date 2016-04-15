#!/usr/bin/perl

open IN, "jAgda.LambdaMaps.js" or die $!;
open OUT, ">LambdaMaps-agda.js" or die $!;
print OUT qq(if (typeof define !== 'function') { var define = require('amdefine')(module) }\n);
while (<IN>) {
  s,"jAgda.Agda.Primitive","./primitive-agda",g;
  print OUT $_;
}
