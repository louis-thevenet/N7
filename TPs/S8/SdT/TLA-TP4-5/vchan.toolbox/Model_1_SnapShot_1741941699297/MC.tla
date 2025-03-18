---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1741941697267406000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1741941697267407000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1741941697267408000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1741941697267409000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1741941697267410000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1741941697267413000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Fri Mar 14 09:41:37 CET 2025 by gss2027
