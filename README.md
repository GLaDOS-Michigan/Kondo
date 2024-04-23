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


## Detailed Instructions

Kondo is designed to relieve developer effort in verifying distributed systems. To evaluate this, we apply two metrics:

1. The user should be responsible for writing fewer invariants
2. The user should be responible for writing fewer lines of proof code

The next two section detail how we obtain these numbers.

### Verifying Claim 1

**Claim:** User's write fewer  



### Verifying Claim 2

TODO: Give an updated table of claims, as the one in paper is out of date.

