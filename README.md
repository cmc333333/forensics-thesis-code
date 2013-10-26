This is a work in progress formalization of a honeynet challenge
(http://old.honeynet.org/scans/scan15/).

It includes two proofs (in honeynet.v):

* lee_honeynet_file - Recreate a timeline proposed by Lee in his Honeynet
  submission, then prove that the hard drive provided satisfies that timeline
* borland_honeynet_file - Recreate evidence Borland provided in his Honeynet
  submission (i.e. that a malicious, deleted gzip was found on the file
  system)

To execute, run the make file, then step through honeynet.v with Coq.

For more details see formalized-forensics.pdf, an in-progress paper written to
accompany this code.
