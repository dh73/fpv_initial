# Initial Blocks for FPV
## Features?
As far as I know, initial procedures for FPV are used in:
* `sva checkers`, where `initial` procedures are valid.
* Simple `assumptions/assertions` in RTL that needs to be checked only once.
* Abstract some values derived from the statement above (for example, start the testing of a cache controller assuming a valid statement where `vld` pin is high and `tags` are different.

## Examples
* part_select [dh].
* selective_initial [cx].
* shift_assume [dh].
* systemverilog_concurrent [dh] <- this is pure systemverilog and Verific is not inferring any `$assert` or `$assume` in none of the examples.
