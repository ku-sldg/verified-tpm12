(in-package "ACL2")

(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/defenum" :dir :system)

(cutil::defenum tpm-startup-type
  (:tpm-st-clear :tpm-st-state :tpm-st-deactivated))               

; saveState from startupData.pvs is defined as save-state1 in tpm.pvs

