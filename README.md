# SharpSSAT

A stochastic Boolean satisfiability(SSAT) solver implemented on top of the model counter 
[SharpSAT](https://github.com/marcthurley/sharpSAT).

## Compile
```
make
```


## Usage


For SSAT solving, run the command:
```
SharpSSAT -s [options] [SDIMACS_File]`
```
options: 
	-q			-quiet mode
    -t [s]		-set time bound to s seconds
	-noCC		-turn off component caching
    -noFreq		-turn off frequency scoring
    -noAct 		-turn off activity scoring
    -noCL  		-turn off clause learning
    -cs [n] 	-set max cache size to n MB
    -p 			-turn on pure literal detection

To enable witness generation, run the command:
```
SharpSSAT -s -k [SDIMACS_File]`
```
then the witness(Skolem functions), written in a BLIF file, will be generated in the same directory as the SDIMACS_File.

## Contact
f you encouter any problems or have suggestions, feel free to create an issue or contact us through r11943096@ntu.edu.tw.


