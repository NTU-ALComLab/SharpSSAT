# SharpSSAT

A stochastic Boolean satisfiability(SSAT) solver implemented on top of the model counter 
[SharpSAT](https://github.com/marcthurley/sharpSAT).

## Compile
```
$ make
```


## Usage


For SSAT solving, run the command:
```
$ SharpSSAT -s [options] [SDIMACS_File]`
```

The default setting is: 
```
$ SharpSSAT -s -p [SDIMACS_FILE]
```

Run `SharpSSAT -h` to see more options.


To enable witness generation, run the command:
```
$ SharpSSAT -s -k [SDIMACS_File]`
```
then the witness (Skolem functions), written in a BLIF file, will be generated in the same directory as the SDIMACS_File.

## Reference
If you are interested in this work, please find our paper in AAAI'23 titled "SharpSSAT: A Strategy Generation Stochastic Boolean Satisfiability Solver"
for reference.

## Contact
If you have any problems or suggestions, please create an issue or contact us at r11943096 @ ntu.edu.


