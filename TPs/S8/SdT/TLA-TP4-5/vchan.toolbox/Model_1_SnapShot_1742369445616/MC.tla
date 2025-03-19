---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742369441577239000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742369441577240000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742369441577241000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742369441577242000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742369441577243000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742369441577246000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:30:41 CET 2025 by gss2027
