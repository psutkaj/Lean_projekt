import LEANprj._02Sequences.AxNIPOfAxCauchyConv
import LEANprj._02Sequences.AxMonoConvOfAxSup
import LEANprj._02Sequences.AxBwOfAxMonoConv
import LEANprj._02Sequences.AxCauchyConvOfAxBw

theorem axSup_iff_axBw : AxSup ↔ AxBW :=
  ⟨axBw_of_axMonoConv ∘ axMonoConv_of_axSup, axSup_of_axNip ∘ axNip_of_axCauchyConv ∘ axCauchyConv_of_axBw⟩
