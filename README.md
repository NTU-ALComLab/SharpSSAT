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

To enable dec-DNNF generation, run the command:
```
$ SharpSSAT -s -d [SDIMACS_File]`
```

To enable certificate generation, run the command:
```
$ SharpSSAT -s -l -p [SDIMACS_File]`
```

## Reference
* [AAAI'23 paper](https://ojs.aaai.org/index.php/AAAI/article/view/25509):
  ```
  @inproceedings{Fan_Jiang_2023,
      author     = {Fan, Yu-Wei and Jiang, Jie-Hong R.},
      title      = {SharpSSAT: A Witness-Generating Stochastic Boolean Satisfiability Solver},
      booktitle  = {Proceedings of the AAAI Conference on Artificial Intelligence},
      DOI        = {10.1609/aaai.v37i4.25509},
      year       = {2023}
   }
  ```
  
## Contact
If you have any problems or suggestions, please create an issue or contact us at r11943096@ntu.edu.tw