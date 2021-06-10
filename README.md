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

## Results
### Formal (SBY) tests
| Test name | Result | Reason |
| --------- | ------ | ------ |
| FIFO (bind) | FAIL | `$initstate` cells not created if assumptions are created in different hierarchy from where the signals are defined (bind) |
| FIFO (no bind) | ERROR | Segfault possibly due `foreach` construct creating assumptions |
| Find values |  PASS | Quite easy test |
| FMDEMO | FAIL | Claire's test, expected to fail |
| Initial test | ERROR | PREUNSAT error, IMO this should work just fine |
| Property equivalence | FAIL | Initial values pass not supported for concurrent assertions |
| Part-select | PASS | Expected pass |
| Shift assume | PASS | Expected pass |

* Total: 3 passing, 3 failing, 2 errors that needs further investigation, Of 8 tests.

---


### Yosys (.ys) tests
| Test name | Result | Reason |
| --------- | ------ | ------ |
| Part select | Verific/Yosys passing | Expected pass |
| Selective initial | Verific/yosys passing | Expected pass |
| Shift assume | Yosys pass, verific pass | Calling the function not from within the initial block |
| Concurrent test ex0 | Verific fail | Initial values pass not supported for concurrent assertions |
| Concurrent test ex1 | Verific fail | Initial values pass not supported for concurrent assertions |
| Concurrent test ex2 | Verific fail | Initial values pass not supported for concurrent assertions |

* Total: 2 passing (Yosys/Verific equivalent), 1 unknown (Verific and yosys not giving the same result), 3 failed, of 6 test.
