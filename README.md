# Algorithms for toric arrangements

This repository contains the [SageMath](https://www.sagemath.org/) algorithms that I developed and used in the toric arrangements sections of my PhD thesis (Chapters 6 and 7 of [\[1\]](#phdthesis)). Please note that the code is (sufficiently) commented to be understood, at least if you follow along the thesis, but needs a major syntax cleanup and a general revision, which I will do whenever I have time and feel like it (i.e., probably not in the foreseeable future).

## Usage

Just load/attach `toric.sage` in your current SageMath session.

## Files description

### toric.sage

This file contains the classes of `ToricEquation`, `ToricLayer`, `ToricArrangement` and `ToricModel` objects. The algorithms that allow to work with these objects are defined as methods.

### toric-aux.sage

This file contains auxiliary functions that are called by the methods in `toric.sage`.

## References

<a id="phdthesis">\[1\]</a> Oscar Papini. _Computational Aspects of Line and Toric Arrangements_. PhD thesis, Università di Pisa (2018). Available at: [https://etd.adm.unipi.it/t/etd-09262018-113931/](https://etd.adm.unipi.it/t/etd-09262018-113931/)