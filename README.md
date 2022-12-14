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

The default setting is: 
```
SharpSSAT -s -p [SDIMACS_FILE]
```

Run `SharpSSAT -h` to see more options.


To enable witness generation, run the command:
```
SharpSSAT -s -k [SDIMACS_File]`
```
then the witness (Skolem functions), written in a BLIF file, will be generated in the same directory as the SDIMACS_File.

## Contact
If you encouter any problems or have suggestions, feel free to create an issue or contact us through r11943096@ntu.edu.tw.


