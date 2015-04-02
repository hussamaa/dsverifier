package br.edu.ufam.dsverifier.domain;

import br.edu.ufam.dsverifier.domain.enums.DigitalSystemRealizations;

public class Implementation {

	private Integer integerBits;
	private Integer precisionBits;
	private Double maximum;
	private Double minimum;
	private Double delta;
	private Long scale;
	private DigitalSystemRealizations realization;

	public Integer getIntegerBits() {
		return integerBits;
	}

	public void setIntegerBits(Integer integerBits) {
		this.integerBits = integerBits;
	}

	public Integer getPrecisionBits() {
		return precisionBits;
	}

	public void setPrecisionBits(Integer precisionBits) {
		this.precisionBits = precisionBits;
	}

	public Double getMaximum() {
		return maximum;
	}

	public void setMaximum(Double maximum) {
		this.maximum = maximum;
	}

	public Double getMinimum() {
		return minimum;
	}

	public void setMinimum(Double minimum) {
		this.minimum = minimum;
	}

	public Double getDelta() {
		return delta;
	}

	public void setDelta(Double delta) {
		this.delta = delta;
	}

	public Long getScale() {
		return scale;
	}

	public void setScale(Long scale) {
		this.scale = scale;
	}

	public DigitalSystemRealizations getRealization() {
		return realization;
	}

	public void setRealization(DigitalSystemRealizations realization) {
		this.realization = realization;
	}

}