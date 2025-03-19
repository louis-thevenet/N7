---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742369385915227000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742369385915228000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742369385915229000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742369385915230000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742369385915231000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742369385915234000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:29:45 CET 2025 by gss2027
