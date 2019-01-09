# Legacy implementation of selected algorithms

This project contains the implementation of implementation for following algorithms solving the Steiner tree problem
parameterized by the number of terminals:

* Dreyfus-Wagner
* Erickson-Monma-Veinott
* Nederlof

You can compile and run the code using following commands:

```
make
./legacy_impl < input_file

The utilized algorithm can be chosen by uncommenting it in the main method of `legacy_impl.cpp`. Note that the main
purpose of this project was development and testing, for the final implementation of Track A submission, please refer to
the `impl` folder in the project root.

Input format description, and a test instance set compatible with this implementation can be found under the of Track A,
in the (PACE 2018 Challenge description)[https://pacechallenge.org/2018/steiner-tree/].
