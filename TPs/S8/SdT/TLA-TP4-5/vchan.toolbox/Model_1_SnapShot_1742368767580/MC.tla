---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742368764549160000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742368764549161000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742368764549162000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742368764549163000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742368764549164000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742368764549167000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:19:24 CET 2025 by gss2027
