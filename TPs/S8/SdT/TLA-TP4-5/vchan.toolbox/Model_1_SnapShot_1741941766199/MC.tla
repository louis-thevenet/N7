---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1741941763147424000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1741941763147425000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1741941763147426000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1741941763147427000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1741941763147428000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1741941763147431000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Fri Mar 14 09:42:43 CET 2025 by gss2027
