theory StateMonad
imports Main
begin

type_synonym A = "int"

datatype State = 
  "state S \<Rightarrow> (A,S)"

definition return :: "A => State" where
  "return x = state \<lambda>(s) = (x,s)" 

definition bind :: "State => (A => State) => State" where
  "state(\<lambda>(s0) = 
     let (a,s1) = runState(m)(s0)
       in runState(f(a))(s1))"

definition seq :: "State => State => State" where
  "state(\<lambda>(s0) = 
    let (a,s1) = runState(m)(s0)
      in runState(s)(s1))"

end
