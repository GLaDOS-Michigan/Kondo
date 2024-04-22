# Notes

Generates async proof from sync proof.

## Commands

Generate monotonicity and message invariants:

```bash
/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Scripts/dafny /msgInvs /ownerInvs distributedSystem.dfy
```

Generate async draft proof:

```bash
/Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/local-dafny/Scripts/dafny /genAsyncProof ../centralized/applicationProof.dfy
```

In this case, the generated draft is the final proof.
