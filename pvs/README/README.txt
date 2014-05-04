The two main TCG specs that I worked off of were TPM Main-Part 2 TPM
Structures and TPM Main-Part 3 TPM Commands. The numbers after the
data and command definitions correspond to the section numbers from
these documents.  

Structures:
Most structures are defined in data.pvs. Those that aren’t defined
there are most likely are not yet implemented. I’ve defined a few of
these within types.pvs, but I don’t think anything from that file is
being used yet. The same goes for tags.pvs. 

Commands:
The commands and command proofs from the TCG spec are declared in
commands.pvs, and the functionality is defined in tpm.pvs. Most
commands have been defined, but some are sill left to do. I think the
input (tpmAbsInput) and output (tpmAbsOutput) have been declared for
most (if not all) commands. I tried to follow as closely to the TCG
spec as I could on those. 

Todo:
Various places have been marked with a “%TODO” tag and a blurb about
what needs to be done. These might be good places to look when first
learning the spec.  

One area that hasn’t been super developed that could easily is
authdata. The file authdata.pvs has the basic definition of authdata,
and all implemented commands have the bare bones of what it is. No
commands yet check the authdata, but most have %TODO markers for where
that should happen.  
