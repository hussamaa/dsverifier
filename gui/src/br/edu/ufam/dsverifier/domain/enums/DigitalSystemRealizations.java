package br.edu.ufam.dsverifier.domain.enums;

public enum DigitalSystemRealizations {

	DFI("Direct Form I"), DFII("Direct Form II"), TDFII("Transposed Direct Form II"), 
	DDFI("Delta Direct Form I"), DDFII("Delta Direct Form II"), TDDFII("Transposed Delta Direct Form II"), 
	CDFI("Cascade Direct Form I"), CDFII("Cascade Direct Form II"), CTDFII("Cascade Transposed Direct Form II"), 
	CDDFI("Cascade Delta Direct Form I"), CDDFII("Cascade Delta Direct Form II"), CTDDFII("Cascade Delta Transposed Direct Form II");

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
