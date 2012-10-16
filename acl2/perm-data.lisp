(in-package "ACL2")

(include-book "cutil/defaggregate" :dir :system)

(include-book "pcr")

(cutil::defaggregate perm-data
  (pcr-attrib)
  :require
  ((pcr-flag-list-p-of-perm-data->pcr-attrib
    (pcr-flag-list-p pcr-attrib)))
  :tag :perm-data)

(defconst *perm-data-init*
  (make-perm-data 
   :pcr-attrib (all-reset-access *pcr-count*)))
