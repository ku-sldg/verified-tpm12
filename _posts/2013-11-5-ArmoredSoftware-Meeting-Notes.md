---
layout: bare
title: Meeting Notes
---

#### AS Meeting Notes - 5 November 2013 - 9:57 AM

#### Agenda

* architecture document
* online presence
  * repos
  * websites
  * using trac
* hiring and students
  * SEWORLD solicitation
  * other publication venures
* status of Xen, OpenStack, and VM status
* schedule and goals

#### Notes

#### Architecture

Went through the architecture and a simple attestation protocol. More
detail present, but no real changes in structure. See the architecture
document in the project repo for more details. No critical decisions
pending, but we do need to think about what the boxes in the diagram
represent - VMs, processes, VPs.

#### Online Presence

* Internal and external repos are up
  * Provide Perry public keys to set up access
  * No content to speak of
  * github is pretty awesome once you figure out that's going on
* External Website with virtually nothing on it for now
* Environment Status
  * Xen is up
  * Identity service up
  * Storage service up
  * Compute node installed
  * Networking is up but hard
  * Two NICs make this hard
* Other possibilities for domain OS
  * CirrOS - found by Leon. Not sure what it is
  * TinyOS - Really a small-system OS, but could be useful
  * Mirage - Mechanism for running Haskell on the OCaml VM
* Demo
  * Would like to have a demo in six months of the basic
    architecture. Even if this is baling wire and chewing gum, we
    should have something to show the sponsor and in public. 

#### To Do Items

* Prasad will start looking at literature on dynamic monitoring
* Andy will continue to look at HaLVM and Mirage (?)
* Leon will continue to get the cloud infrastructure up
  * Look at alternative VM frameworks
  * Get a basic Xen cloud up and running
* Perry will continue the architecture document
  * Populate websites and repos
  * Monthly report
* All will send Perry public keys to access the git repos
