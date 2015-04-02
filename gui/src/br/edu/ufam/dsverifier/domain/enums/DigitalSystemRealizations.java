package br.edu.ufam.dsverifier.domain.enums;

public enum DigitalSystemRealizations {

	DFI("Direct Form I"), DFII("Direct Form II"), TDFII("Transposed DFI"), 
	DDFI("Delta DFI"), DDFII("Delta DFII"), TDDFII("Transposed Delta DFII"), 
	CDFI("Cascade DFI"), CDFII("Cascade DFII"), CTDFII("Cascade Transposed DFII"), 
	CDDFI("Cascade Delta DFI"), CDDFII("Cascade Delta DFII"), CTDDFII("Cascade Delta Transposed DFII");

	private String realization;

	private DigitalSystemRealizations(String realization) {
		this.realization = realization;
	}

	public String getRealization() {
		return realization;
	}

	public void setRealization(String realization) {
		this.realization = realization;
	}

}
