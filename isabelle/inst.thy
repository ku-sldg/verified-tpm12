theory inst
imports Main List
begin

text{*
  Define types for index and hash.  Note there is currently no upper index value.
*}

type_synonym hash = int
type_synonym index = nat

text{*Define type for PCRs that allows two reset values and an extension operator*}
datatype PCR = reset | resetOne | extend PCR hash

text{*PCRs is a function mapping indexs to PCRs.  Use function update to model extend operator.*}
type_synonym PCRs = "index => PCR"

text{*A simple function to extend a single PCR*}
definition extendPCR :: "index => hash => PCRs => PCRs" where
"extendPCR i h pcrs = pcrs(i:=extend(pcrs(i))(h))"

type_synonym KEY_VAL = int

definition private :: "KEY_VAL => KEY_VAL" where "private k = -(abs k)"
definition public :: "KEY_VAL => KEY_VAL" where "public k = (abs k)"

datatype PCR_SELECT = pcr_select "(nat list)"

datatype PCR_COMPOSITE = pcr_composite PCRs PCR_SELECT

datatype KEY_USAGE = Signing | Encryption | AIK

datatype KEY_FLAGS = Dummy

datatype tpmNonce = tpmNonce hash
fun wellFormedNonce :: "tpmNonce => bool" where
"wellFormedNonce (tpmNonce h) = True"

datatype tpmSessionKey = tpmSessionKey KEY_VAL
fun wellFormedSessionKey :: "tpmSessionKey => bool" where
"wellFormedSessionKey (tpmSessionKey x) = (x > 0)"

datatype tpmKey = tpmKey KEY_VAL KEY_USAGE KEY_FLAGS PCR_COMPOSITE KEY_VAL
fun wellFormedKey :: "tpmKey => bool" where
"wellFormedKey (tpmKey _ _ _ _ _) = True"

datatype tpmQuote = tpmQuote tpmNonce PCR_COMPOSITE KEY_VAL
fun wellFormedQuote :: "tpmQuote => bool" where
"wellFormedQuote (tpmQuote n _ k) = ((wellFormedNonce n) \<and> (k > 0))"

definition powerOn :: "PCRs => PCRs" where
"powerOn p = (\<lambda> i . resetOne)"

definition senter :: "PCRs => PCRs" where
"senter p = (\<lambda> i . reset)"

theorem powerOn_senter [simp] : "senter (powerOn p) = senter p"
by (simp add: senter_def)

text{* why is this here?  Of course extend is reflexive. *}
value "extend (extend reset 5) 6 = extend (extend reset 5) 6"

theorem unique_extend [simp] : "((extend p h1) = (extend p h2)) \<longleftrightarrow> (h1 = h2)"
  by simp_all

theorem not_symetric [simp] : "(extend (extend p h1) h2) = (extend (extend p h2) h1) \<longleftrightarrow> (h1=h2)"
  by auto

text{*Abstract definitions for some basic commands*}
datatype tpmCommand =
  ABS_Reset | ABS_Init | ABS_Startup | ABS_Extend index hash | ABS_Quote tpmNonce PCR_SELECT

type_synonym tpmAbsInput = "tpmCommand list"

datatype tpmAbsOutput = 
  OUT_Err | OUT_None | OUT_Quote tpmQuote

record State = 
  out :: "tpmAbsOutput list"
  EK :: "KEY_VAL"
  SRK :: "KEY_VAL"
  pcrs :: "PCRs"

definition initState :: State where
"initState = (| out=[],EK=0,SRK=1,pcrs=(\<lambda> x. resetOne) |)"

fun execute :: "tpmCommand => State => State" where
"execute ABS_Init s = s(| out:=[OUT_None], pcrs:=(\<lambda> x . resetOne) |)" |
"execute ABS_Reset s = s(| out:=[OUT_None], pcrs:=(\<lambda> x . resetOne) |)" |
"execute ABS_Startup s = s(| out:=((out s)@[OUT_None]), pcrs:=(\<lambda> x . resetOne) |)" |
"execute (ABS_Extend i h) s = s(| out:=((out s)@[OUT_None]), pcrs:=extendPCR i h (pcrs s) |)" |
"execute (ABS_Quote n sel) s = s(| out:=(out s)@[(OUT_Quote (tpmQuote n (pcr_composite (pcrs s) sel) 0))] |)" text{*not using AIK yet*}

definition execute_star :: "tpmAbsInput => State => State" where
"execute_star program s = fold execute program s"

value "(execute_star [ABS_Reset,ABS_Extend 1 1] initState)"

text{*
  Reset in a command sequence always resets
*}

lemma "(EK (execute_star (i@[ABS_Reset]) s)) = (EK (execute_star i s))"
by (auto simp add: execute_star_def)

lemma "(SRK (execute_star (i@[ABS_Reset]) s)) = (SRK (execute_star i s))"
by (auto simp add: execute_star_def)

lemma "(pcrs (execute_star (i@[ABS_Reset]) s)) = (pcrs initState)"
by (auto simp add: execute_star_def initState_def)

lemma "(out (execute_star (i@[ABS_Reset]) s)) = [OUT_None]"
by (auto simp add: execute_star_def initState_def)

lemma EK_invariant[simp]: "(EK (execute c s)) = (EK s)"
apply(induct c)
apply(auto)
done

lemma EK_invariant[simp]: "EK (execute_star cl s) = (EK s)"
apply(induct cl)
apply(auto simp add: execute_star_def)
oops

lemma SRK_invariant[simp]: "(SRK (execute c s)) = (SRK s)"
apply(induct c)
apply(auto)
done

lemma "(EK (execute_star (i@[ABS_Reset]@j) s)) = (EK (execute_star ([ABS_Reset]@j) s))"
apply(auto simp add: execute_star_def)
oops
