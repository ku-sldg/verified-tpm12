# This makefile will only work on the UT filesystem.  I thought about
# including the Makefile-generic file as part of this repo, but I
# didn't want to think about GPL2 issues associated with
# Makefile-generic yet.

ACL2=~ragerd/r/acl2-devel/ccl-saved_acl2

all: top.cert startup-data.cert

# pcr.cert: pcr.lisp

#crypto.cert: crypto.lisp
crypto.cert: pcr.cert

key.cert: crypto.cert

perm-data.cert: pcr.cert

tpm.cert: pcr.cert
tpm.cert: crypto.cert
tpm.cert: key.cert
tpm.cert: perm-flags.cert
tpm.cert: perm-data.cert
tpm.cert: memory.cert

top.cert: tpm.cert 

include ~ragerd/r/acl2-devel/books/Makefile-generic
