theory pcr
imports Main
begin

text{*Define types for index and hash.  Note there is currently no upper index value.*}

type_synonym hash = int
type_synonym index = nat

text{*Define type for PCRs that allows two reset values and an extension operator*}

datatype PCR = reset | resetOne | extend PCR hash

text{*PCRs is a function mapping indexs to PCRs.  Use function update to model extend operator.*}
type_synonym PCRs = "index => PCR"

text{*A simple function to extend a single PCR*}
definition extendPCR :: "index => hash => PCRs => PCRs" where
"extendPCR i h pcrs = pcrs(i:=extend(pcrs(i))(h))"

text{*Abstract definitions for some basic commands*}
datatype tpmAbsInput =
  ABS_Reset | ABS_Init | ABS_Startup | ABS_Extend index hash

datatype tpmAbsOutput = 
  OUT_PCRs PCRs | OUT_Err

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

type_synonym State = "PCRs => tpmAbsOutput \<times> PCRs"

definition return :: "tpmAbsOutput => State" where
"return a = (\<lambda> s . (a,s))"

definition bind :: "State => (tpmAbsOutput => State) => State" where
"bind m f = (\<lambda> s0 . let (a,s1) = m(s0) in (f(a))(s1))"

definition runState :: "PCRs => State => tpmAbsOutput \<times> PCRs" where
"runState pcrs s = s pcrs"

value "OUT_PCRs (\<lambda> x . reset)"
value "return (OUT_PCRs (\<lambda> x . reset))"
value "(return (OUT_PCRs (\<lambda> x . reset)) (\<lambda> x . reset))"
value "(bind (return (OUT_PCRs (\<lambda> x . reset)))
         (\<lambda> x::tpmAbsOutput . (\<lambda> y::PCRs . (OUT_Err,(\<lambda> x . resetOne))))) (\<lambda> x . reset)"
value "let (x,p) = (bind (return (OUT_PCRs (\<lambda> x . reset)))
         (\<lambda> x::tpmAbsOutput . (\<lambda> y::PCRs . (OUT_Err,extendPCR(0)(1)(y))))) (\<lambda> x . reset) in p(0)"

text{*Executing a command should be a case statement over abstract inputs.*}

end
