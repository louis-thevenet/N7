---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1741941939307433000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1741941939307434000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1741941939307435000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1741941939307436000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1741941939307437000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1741941939307440000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Fri Mar 14 09:45:39 CET 2025 by gss2027
