---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742368775697181000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742368775697182000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742368775697183000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742368775697184000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742368775697185000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742368775697188000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:19:35 CET 2025 by gss2027
