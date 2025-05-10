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

Run `SharpSSAT` to see more options.


To enable witness generation, run the command:
```
$ SharpSSAT -s -k [SDIMACS_File]`
```
then the witness (Skolem functions), written in a BLIF file, will be generated in the same directory as the SDIMACS_File.

To enable dec-DNNF generation, run the command:
```
$ SharpSSAT -s -d [NNF_Output] [SDIMACS_File]`
```

To enable certificate generation, run the command:
```
$ SharpSSAT -s -l -p [SDIMACS_File]`
```

To enable solving instances with universal quantifiers, run the command:
```
$ SharpSSAT -s -e [SDIMACS_File]`
```

Witness generation (strategy extraction) can be enabled when solving instances with universal quantifiers. In such cases, two strategy functions will be generated in the same directory as the SDIMACS_File.

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

* [IJCAI'24 paper](https://doi.org/10.24963/ijcai.2024/206):
  ```
  @inproceedings{cheng_knowledge_2024,
    title     = {Knowledge Compilation for Incremental and Checkable Stochastic Boolean Satisfiability},
    author    = {Cheng, Che and Luo, Yun-Rong and Jiang, Jie-Hong R.},
    booktitle = {Proceedings of the Thirty-Third International Joint Conference on Artificial Intelligence, {IJCAI-24}},
    publisher = {International Joint Conferences on Artificial Intelligence Organization},
    editor    = {Kate Larson},
    pages     = {1862--1872},
    year      = {2024},
    month     = {8},
    note      = {Main Track},
    doi       = {10.24963/ijcai.2024/206},
    url       = {https://doi.org/10.24963/ijcai.2024/206},
  }
  ```
  
## Contact
If you have any problems or suggestions, please create an issue or contact us at Che Cheng f11943097@ntu.edu.tw
