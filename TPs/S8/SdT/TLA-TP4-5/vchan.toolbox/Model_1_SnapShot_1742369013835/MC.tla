---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742369010787192000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742369010787193000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742369010787194000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742369010787195000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742369010787196000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742369010787199000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:23:30 CET 2025 by gss2027
