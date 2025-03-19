---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742368708336150000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742368708336151000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742368708336152000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742368708336153000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742368708336154000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742368708336157000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:18:28 CET 2025 by gss2027
