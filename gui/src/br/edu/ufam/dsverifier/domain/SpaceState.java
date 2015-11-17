package br.edu.ufam.dsverifier.domain;

public class SpaceState {

	private String matrixA;
	
	private String matrixB;
	
	private String matrixC;
	
	private String matrixD;
	
	private String matrixFeedback;
	
	private boolean isClosedLoop;
	
	private String inputs;
	
	private Integer nStates;
	
	private Integer nInputs;
	
	private Integer nOutputs;
	
	private Integer integerBits;
	
	private Integer precisionBits;
	
	private double errorLimit;

	public String getMatrixA() {
		return matrixA;
	}

	public void setMatrixA(final String matrixA) {
		this.matrixA = matrixA;
	}

	public String getMatrixB() {
		return matrixB;
	}

	public void setMatrixB(final String matrixB) {
		this.matrixB = matrixB;
	}

	public String getMatrixC() {
		return matrixC;
	}

	public void setMatrixC(final String matrixC) {
		this.matrixC = matrixC;
	}

	public String getMatrixD() {
		return matrixD;
	}

	public void setMatrixD(final String matrixD) {
		this.matrixD = matrixD;
	}

	public String getInputs() {
		return inputs;
	}

	public void setInputs(final String inputs) {
		this.inputs = inputs;
	}

	public Integer getnStates() {
		return nStates;
	}

	public void setnStates(final Integer nStates) {
		this.nStates = nStates;
	}

	public Integer getnInputs() {
		return nInputs;
	}

	public void setnInputs(final Integer nInputs) {
		this.nInputs = nInputs;
	}

	public Integer getnOutputs() {
		return nOutputs;
	}

	public void setnOutputs(final Integer nOutputs) {
		this.nOutputs = nOutputs;
	}

	public Integer getIntegerBits() {
		return integerBits;
	}

	public void setIntegerBits(final Integer integerBits) {
		this.integerBits = integerBits;
	}

	public Integer getPrecisionBits() {
		return precisionBits;
	}

	public void setPrecisionBits(final Integer precisionBits) {
		this.precisionBits = precisionBits;
	}

	public double getErrorLimit() {
		return errorLimit;
	}

	public void setErrorLimit(final double errorLimit) {
		this.errorLimit = errorLimit;
	}

	public String getMatrixFeedback() {
		return matrixFeedback;
	}

	public void setMatrixFeedback(final String matrixFeedback) {
		this.matrixFeedback = matrixFeedback;
	}

	public boolean isClosedLoop() {
		return isClosedLoop;
	}

	public void setClosedLoop(final boolean isClosedLoop) {
		this.isClosedLoop = isClosedLoop;
	}

}