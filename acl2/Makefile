# This makefile will only work on the UT filesystem

ACL2=/u/ragerdl/r/acl2-devel/ccl-saved_acl2hp

all: tpm.cert

# pcr.cert: pcr.lisp

#crypto.cert: crypto.lisp
crypto.cert: pcr.cert

key.cert: crypto.cert

tpm.cert: pcr.cert
tpm.cert: crypto.cert
tpm.cert: key.cert
tpm.cert: perm-flags.cert
tpm.cert: perm-data.cert

top.cert: tpm.cert 

include /u/ragerdl/r/acl2-devel/books/Makefile-generic
