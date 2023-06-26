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
* [AAAI 2023]:
  ```
  @inproceedings{Fan:AAAI23,
      author      = {Yu-Wei Fan and Jie-Hong Roland Jiang},
      title       = {SharpSSAT: A Witness-Generating Stochastic Boolean Satisfiability Solver},
      booktitle   = {In Proceedings of the AAAI Conference on Artificial Intelligence (AAAI)},
      year        = {2023}
  }
  ```

## Contact
If you have any problems or suggestions, please create an issue or contact us at r11943096 @ ntu.edu.


