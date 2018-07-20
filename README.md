# WelderToolbox

This project started from a proof of the group properties of an elliptic curve that we wrote for Welder in 2017.  It is a completion of the proof done there and includes the addition of tactics to automate the good repository that this project provided us with. 

## Verified Elliptic Curve Cryptography (VEC)

You will find under ./vec the Verified Elliptic Curve Cryptography (VEC) project. The proof this project contains will no longer be supported in future versions of Welder but provides a good example of the challenges we where facing at the time which motivated some of its developments. 

You will find under ./vec/documents interesting help to get started with Welder. The presentation, report and useful information to integrate the proof assistant, the proof and the solver on Intellij Idea are still valid. The documentation will most probably be superseded by future changes in the tool. 

## The ToolBox

You will find under ./Tactics.scala the implemented tactics for the system.

You will find under ./welder-rewriter the implemention of a rewriter following the book "Term rewriting and all that". This should be included in Welder in the future. 

## Future directions

To get an idea of our current interests you will find in ./articles papers that we have explore until now. 
