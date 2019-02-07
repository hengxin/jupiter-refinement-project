# `jupiter-refinement-project`

## What is this project about?
This project is devoted to
"formal specification and verification of a family of Jupiter protocols 
for implementing replicated lists".

Jupiter protocol is a core of many collaborative editing systems.

## TLA+ Modules
The following figure shows the key modules in this project,
where the solid line from module A to module B indicates that B "extends" A,
and the dashed line from module A to module B indicates that B contains an "instance" of A.

![Module Graph](https://github.com/hengxin/jupiter-refinement-project/wiki/modules.png)

These modules fall into four categories:
- System Model:
  It describes the client/server architecture of collaborative editing systems.

  It also models a replica as an abstract state machine 
  and provides the interface for implementing such a state machine.
- Jupiter Family: 
  This contains several techniques for all Jupiter protocols.
  - `JupiterCtx` is for context-based Jupiter protocols.
  - `JupiterSerial` helps to establish the serialization order at the server.
  - `BufferStateSpace`, `GraphStateSpace`, `SetStateSpace` are data structures for supporting OTs in Jupiter protocols.
- Jupiter Protocols: 
  Formal TLA+ specifications of four Jupiter protocols, 
  namely `AJupiter`, `XJupiter`, `CJupiter`, and `AbsJupiter`.
- Refinement: 
  The (data) refinement relations among Jupiter protocols are established.
  Specifically, 
  - `AJupiter` is a refinement (a.k.a implementation) of `XJupiter`,
  - `XJupiter` is a refinement of `CJupiter`, 
  - `CJupiter` is a refinement of `AbsJupiter`.

## How to run it?

There are two ways to run model checking on these specifications of Jupiter protocols:

1. Run separately.

Create and run TLC models in the usual way; 
see the "Model Checking" page in TLC toolbox's Help.
2. Run in batch.

We write scripts to automatically conduct a batch of experiments;
see [tangruize/jupiter-experiments](https://github.com/tangruize/jupiter-experiments/tree/master).

---
For more details, please visit the [wiki](https://github.com/hengxin/jupiter-refinement-project/wiki) page.

If you have any questions, please fire an issue or contact us (hfwei at nju dot edu dot cn).
