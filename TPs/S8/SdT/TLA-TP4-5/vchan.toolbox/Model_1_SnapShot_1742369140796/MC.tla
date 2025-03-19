---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742369137762215000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742369137762216000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742369137762217000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742369137762218000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742369137763219000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742369137763222000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:25:37 CET 2025 by gss2027
