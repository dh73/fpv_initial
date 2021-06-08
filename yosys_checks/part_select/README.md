# Part-select value selection
## Assertion type
This module creates an assumption under an initial block for an input value, depending on the values that are read from a `$readmemb` construct in a separate `initial` block. See code block below.

```verilog
   initial $readmemb("init.bin", test);
   
   initial begin
      if (test[1][4] && test[3][4]) assume (kind == 2'b10);
      else assume (kind == 2'b11);
   end
```
## SBY File
This is a bounded check with depth = 1, because the evaluation of the initial assumption is valid only during the first cycle.
If the assumption within the initial construct is not elaborated, the model evaluates `assert (0)` causing a failure.
