---- MODULE MC ----
EXTENDS vchan, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxReadLen
const_1742368535186111000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MaxWriteLen
const_1742368535186112000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2BufferSize
const_1742368535186113000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3Byte
const_1742368535186114000 == 
1..5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1742368535186115000 ==
Len(Sent) < 4
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1742368535186118000 ==
Len(Got) < 6
----
=============================================================================
\* Modification History
\* Created Wed Mar 19 08:15:35 CET 2025 by gss2027
