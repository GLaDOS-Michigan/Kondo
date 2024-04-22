# Kondo

This is the code base for the Kondo prototype, as decribed in the OSDI'24 paper
"Inductive Invariants That Spark Joy: Using Invariant Taxonomies to Streamline Distributed Systems Proofs".

The paper introduces the concept of an Invariant Taxonomy that factors the invariants of a distributed protocol
into Protocol Invariants and Regular Invariants. Kondo is a tool that helps developers automatically generate
"Regular Invariants" for their distributed protocol, and lift a simpler, synchronous proof of the protocol
to the general asynchronous setting.

The following instructions have been tested on an M3 MacBook Pro running MacOS Sonoma.

## Project Layout

This artifact has two main directories.

### local-dafny/

The directory local-dafny/ contains the source code and executable for the Kondo tool. It is a fork of
[Dafny 4.2.0](https://github.com/dafny-lang/dafny/releases/tag/v4.2.0).

The core Kondo functionality is implemented in the local-dafny/Source/DafnyCore/Kondo/ sub-directory.

### kondoPrototypes/

The directory kondoPrototypes/ contains the protocols on which Kondo is evaluated, together with the scripts
for performing the evaluation.

## Dependencies

Dotnet 6.0 [runtime](https://dotnet.microsoft.com/en-us/download/dotnet/6.0/runtime?cid=getdotnetcore&os=macos&arch=arm64)

Building local dafny [instructions](https://github.com/dafny-lang/dafny/wiki/INSTALL#install-the-binaries)

```bash
cd local-dafny
make
```

## Getting Started Instructions

Getting Started Instructions

## Detailed Instructions

### Artifact Claims

Aritfact claims

TODO: Give an updated table of claims, as the one in paper is out of date.

### Verifying Claim 1

### Verifying Claim 2

TODO

