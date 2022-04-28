# Paper-Benchmarks/SLL
Port of singly-linked list tests from
`src/test/resources/synthesis/paper-benchmarks/sll` to use sequences instead

## Works
| Name         | Any Notes                                              |
|--------------|--------------------------------------------------------|
|ssl-singleton |                                                        |
|ssl-dupleton  |                                                        |
|ssl-free      |                                                        |
|ssl-copy      |                                                        |
|ssl-append    |                                                        |

## Doesn't work
| Name         | Reason                                      |
|--------------|---------------------------------------------|
| ssl-init     | Haven't defined `<=` (subset) for sequences (OpSubinterval) |
| ssl-delete-all | Haven't defined `--` (difference) on sequences (OpDiff) |