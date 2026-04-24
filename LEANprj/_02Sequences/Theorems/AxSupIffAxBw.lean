import LEANprj._02Sequences.Theorems.AxNIPOfAxCauchyConv
import LEANprj._02Sequences.Theorems.AxMonoConvOfAxSup
import LEANprj._02Sequences.Theorems.AxBwOfAxMonoConv
import LEANprj._02Sequences.Theorems.AxCauchyConvOfAxBw

theorem axSup_iff_axBw : AxSup ↔ AxBW :=
  ⟨axBw_of_axMonoConv ∘ axMonoConv_of_axSup, axSup_of_axNip ∘ axNip_of_axCauchyConv ∘ axCauchyConv_of_axBw⟩
