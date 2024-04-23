# Kondo

This is the code base for the Kondo prototype, as decribed in the OSDI'24 paper
"Inductive Invariants That Spark Joy: Using Invariant Taxonomies to Streamline Distributed Systems Proofs".

The paper introduces the concept of an Invariant Taxonomy that factors the invariants of a distributed protocol
into Protocol Invariants and Regular Invariants. Kondo is a tool that helps developers automatically generate
"Regular Invariants" for their distributed protocol, and lift a simpler, synchronous proof of the protocol
to the general asynchronous setting.

## Project Layout

This artifact has two main directories.

### local-dafny/

The directory local-dafny/ contains the source code and executable for the Kondo tool. It is a fork of
[Dafny 4.2.0](https://github.com/dafny-lang/dafny/releases/tag/v4.2.0).

The core Kondo functionality is implemented in the local-dafny/Source/DafnyCore/Kondo/ sub-directory.

### kondoPrototypes/

The directory kondoPrototypes/ contains the protocols on which Kondo is evaluated, together with the scripts for performing the evaluation.

## Getting Started Instructions

The following instructions have been tested on an M3 MacBook Pro running MacOS Sonoma. Libraries and commands for other OS may differ.

### Build And Test Local Dafny

We begin with building our local version of Dafny that contains Kondo extensions. 

1. Dependencies:
	* Install .NET SDK (version 6.0)
		* This can be done using brew: `brew install dotnet-sdk`,
		* Or through a manual install [https://dotnet.microsoft.com/en-us/download/dotnet/6.0](https://dotnet.microsoft.com/en-us/download/dotnet/6.0)
	* [python3 and pip3 are needed but they are likely already part of the Mac installation]
* Build Dafny. From the project root:

	```bash
	cd local-dafny
	make
	```
* To check that Dafny runs as expected, run from the local-dafny directory:

	```bash
	 ./Scripts/dafny /compile:0 test.dfy
	```
	The expected output is
	> `Dafny program verifier finished with 1 verified, 0 errors`
	
### Verifying Protocols

Now that Dafny is set up, we check that all 10 protocols in our evaluation passes the dafny verifier. 

```bash
cd kondoPrototypes/
./verify-all 
```
Note that warnings of the form `Warning: /!\ No terms found to trigger on.` can be ignored

This script runs the dafny verifier on each of the protocol, and takes about 5min on an M3 MacBook Pro. Note that for each protocol, there are three versions:

1. Manual: This is fully manual proof of the asynchronous protocol (i.e. what a user would do without Kondo)
2. Sync: This is a synchronous proof of the protocol, and serves as the input to Kondo (step 1 in Figure 6)
3. Kondo: This is the Kondo-generated asynchronous protocol

One may also verify each version of each protocol individually, by running the `verify` script in the respective sub-directory for the protocol version. For instance:

```bash
./kondoPrototypes/clientServer/sync/verify
```


## Detailed Instructions

This section involves reproducing the results published in the paper. Note that Kondo's capabilities has advanced since the original accepted manuscript, and as a result the Evaluation section in the camera-ready paper will be different from the original version. The instructions here present the expected results in the updated Evaluation, and how to reproduce them.

The main addition to Kondo is that Kondo now automatically generates a draft of the final proof (box 5 in Figure 6). As such, the user is only responsible for completing the proof of the synchronous protocol (box 5 in Figure 6).


Kondo's goal is to relieve developer effort in verifying distributed systems. To evaluate this, we apply two metrics:

1. The user should be responsible for writing fewer invariants
2. The user should be responible for writing fewer lines of proof code

The next two section detail how we obtain these numbers.

### Verifying Claim 1

**Claim:** Users write fewer invariants when using Kondo. 

To evaluate this claim, we compare the number of invariant clauses a user would have to manually derive and prove when using Kondo, compared to the baseline of not using Kondo. The table below presents the numbers.

| protocol                   | without Kondo | with Kondo |
|----------------------------|---------------|------------|
| Client-Server              | 5             | 1          |
| Ring Leader Election       | 6             | 1          |
| Simplified Leader Election | 7             | 3          |
| Two-Phase Commit           | 8             | 4          |
| Paxos                      | 27            | 20         |
| Flexible Paxos             | -             | 21         |
| Distributed Lock           | 2             | 0          |
| ShardedKV                  | 2             | 0          |
| ShardedKV-Batched          | 2             | 0          |
| Lock Server                | 7             | 1          |

#### "With Kondo" Column

The numbers in this table are all obtained through manual inspection. To derive the "with Kondo" figures for a protocol, look at `applicationProof.dfy` file in the `sync/` sub-directory, e.g., `kondoPrototypes/paxos/sync/applicationProof.dfy`. This file contains the proof of the synchronous protocol, and it's inductive invariant. The number of invariants clauses is found in the predicate `ProtocolInv(c: Constants, v: Variables)`. 

Note that each clause in `ProtocolInv` may count as more than one invariant, should it contain more that one sub-clause. In that case, the actual number is marked as a comment. For example, the following `ProtocolInv` definition would show that 

```C#
// Protocol bundle: 4 clauses in total
ghost predicate ProtocolInv(c: Constants, v: Variables)
  requires v.WF(c)
{
  && Invariant_A(c, v)
  && Invariant_B(c, v)
  && Invariant_C(c, v)  // 2
}
```

there are 4 clauses in total, as `Invariant_C` accounts for 2 of them.

#### "Without Kondo" Column

To derive the "without Kondo" figures for a protocol, we look at two files: 

1. `applicationProof.dfy` file in the `manual/` sub-directory, e.g., `kondoPrototypes/paxos/manual/applicationProof.dfy`. This file contains a fully manual proof of the asynchronous protocol.
2. `messageInvariants.dfy` file in the `manual/` sub-directory, e.g. `kondoPrototypes/paxos/manual/messageInvariants.dfy`. This file contains helper lemmas used in the final asynchronous protocol proof. 

The total number of invariants clauses is found in the predicate `ProtocolInv(c: Constants, v: Variables)` in `applicationProof.dfy`, and predicate `MessageInv(c: Constants, v: Variables)` in `messageInvariants.dfy` (note that the conjunct `v.WF(c)` is always omitted from the count). 



### Verifying Claim 2

**Claim:** Users write fewer lines of proof code

| protocol                   | without Kondo | with Kondo |
|----------------------------|---------------|------------|
| Client-Server              | 93            | 40         |
| Ring Leader Election       | 191           | 63         |
| Simplified Leader Election | 125           | 94         |
| Two-Phase Commit           | 184           | 133        |
| Paxos                      | 850           | 557        |
| Flexible Paxos             | -             | 554        |
| Distributed Lock           | 64            | 31         |
| ShardedKV                  | 178           | 61         |
| ShardedKV-Batched          | 178           | 31         |
| Lock Server                | 267           | 44         |




