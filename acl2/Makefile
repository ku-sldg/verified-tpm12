# This makefile will only work on the UT filesystem.  I thought about
# including the Makefile-generic file as part of this repo, but I
# didn't want to think about GPL2 issues associated with
# Makefile-generic yet.

ACL2=~ragerd/r/acl2-devel/ccl-saved_acl2

all: top top.cert

crypto.cert: pcr.cert

key.cert: crypto.cert

tpm-input.cert: key.cert
tpm-input.cert: $(DIRS)

perm-data.cert: pcr.cert

tpm.cert: pcr.cert
tpm.cert: crypto.cert
tpm.cert: key.cert
tpm.cert: perm-flags.cert
tpm.cert: perm-data.cert
tpm.cert: memory.cert
tpm.cert: tpm-input.cert
tpm.cert: startup-data.cert

top.cert: tpm.cert 

DIRS = lib

include ~ragerd/r/acl2-devel/books/Makefile-generic
include ~ragerd/r/acl2-devel/books/Makefile-subdirs
