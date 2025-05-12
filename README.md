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
$ SharpSSAT -s [-p] [-k] [-d <NNF_Output>] [-l] [-u] <SDIMACS_File>
```

* `<SDIMACS_File>`: The name of the input SSAT formula in `.sdimacs` format.
* `-p`: Enables pure literal elimination. (optional)
* `-k`: Enables witness generation. The witness (Skolem functions), written in a BLIF file, will be generated in the same directory as `<SDIMACS_File>`. (optional)
* `-d <NNF_Output>`: Enables dec-DNNF generation and specifies the NNF output file. Cannot be used with the option `-u`. (optional)
* `-l`: Enables certificate generation. Cannot be used with the option `-u`. (optional)
* `-u`: Enables solving instances with universal quantifiers.  Cannot be used with the options `-d` and `-l`. When used with `-k`,  two strategy functions, written in separate BLIF files (`<SDIMACS_File>_exist.blif` for existential variables and `<SDIMACS_File>_univ.blif` for universal variables), will be generated in the same directory as `<SDIMACS_File>`. (optional)

Run `SharpSSAT` to see more available options.


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
