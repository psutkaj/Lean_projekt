import LEANprj._02Sequences.Theorems.AxNIPOfAxCauchyConv
import LEANprj._02Sequences.Theorems.AxMonoConvOfAxSup
import LEANprj._02Sequences.Theorems.AxBwOfAxMonoConv
import LEANprj._02Sequences.Theorems.AxCauchyConvOfAxBw


theorem axSup_iff_axBw :
  AxSup ↔ AxBW :=
by
  constructor
  · intro ax_sup
    apply axBw_of_axMonoConv
    apply axMonoConv_of_axSup
    exact ax_sup
  · intro ax_bw
    apply axSup_of_axNip
    apply axNip_of_axCauchyConv
    apply axCauchyConv_of_axBw
    exact ax_bw
