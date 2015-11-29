package br.edu.ufam.dsverifier.util;

import java.io.File;
import java.io.IOException;
import java.math.BigDecimal;
import java.math.RoundingMode;

import javafx.scene.Node;
import javafx.scene.control.CheckBox;
import javafx.scene.control.TextField;
import javafx.scene.layout.GridPane;
import br.edu.ufam.dsverifier.domain.SpaceState;

public class SpaceStateUtils {

	private static SpaceStateUtils instance;

	private SpaceStateUtils() {
	}

	public static SpaceStateUtils getInstance() {
		if (instance == null) {
			instance = new SpaceStateUtils();
		}
		return instance;
	}

	/**
	 * Method to transform the string value to integer value.
	 */
	public static int parserFieldInteger(final TextField field) {

		if (field.getText().toString().isEmpty()) {
			return 0;
		}

		return Integer.parseInt(field.getText().toString());
	}

	/**
	 * Method to check if the indexes of matrix is really correct
	 */
	public static boolean validateSpaceStateConstants(final int pInputs,
			final int qOutputs, final int nStates) {
		return ((pInputs > 0) && (qOutputs > 0) && (nStates > 0));
	}

	public static String getValuesFromGrid(final GridPane grid,
			final int numRows, final int numColumns) {
		final StringBuilder line = new StringBuilder();
		int countColumns = 0;
		int countRows = 0;
		final int maxNodes = numRows * numColumns;
		line.append("[");
		for (final Node node : grid.getChildren()) {
			if (node instanceof TextField) {
				final double cell = Double.parseDouble(((TextField) node)
						.getText().toString());
				final BigDecimal value = new BigDecimal(cell).setScale(1,
						RoundingMode.HALF_EVEN);
				line.append(value);
				countColumns++;
				countRows++;

				if (countColumns != numColumns) {
					line.append(",");
				}

				if (countColumns == numColumns && countRows != maxNodes) {
					countColumns = 0;
					line.append(";");
				}
			}
		}
		line.append("]");
		return line.toString();
	}

	public void createVerificationSpaceStateFile(final int integerBits,
			final int precisionBits, final double errorLimit, final boolean isClosedLoop) throws IOException {
		final StringBuilder spaceState = new StringBuilder();
		SpaceState spaceStateObject = new SpaceState();

		spaceStateObject = FileUtils.readFile("file_temp.ss");
		spaceStateObject.setErrorLimit(errorLimit);
        
		prepareSpaceStateVerification(integerBits, precisionBits, spaceState,
				spaceStateObject, isClosedLoop);
		
		FileUtils.createFile("file.ss", spaceState.toString());
		FileUtils.deleteFile(new File("file_temp.ss"));
	}

	private void prepareSpaceStateVerification(final int integerBits,
			final int precisionBits, final StringBuilder spaceState,
			final SpaceState spaceStateObject, final boolean isClosedLoop) {
		spaceState.append("implementation <" + integerBits + ","
				+ precisionBits + ">\n");
		spaceState.append("state = " + spaceStateObject.getnStates() + ";\n");
		spaceState.append("inputs = " + spaceStateObject.getnInputs() + ";\n");
		spaceState
				.append("outputs = " + spaceStateObject.getnOutputs() + ";\n");
		spaceState.append(spaceStateObject.getMatrixA() + "\n");
		spaceState.append(spaceStateObject.getMatrixB() + "\n");
		spaceState.append(spaceStateObject.getMatrixC() + "\n");
		spaceState.append(spaceStateObject.getMatrixD() + "\n");
		spaceState.append(spaceStateObject.getInputs());
		if (isClosedLoop){
			spaceState.append("\n" +spaceStateObject.getMatrixFeedback());
		}
	}

	public static boolean isValidSpaceStateInputs(final TextField inputs,
			final TextField outputs, final TextField stateVariables) {

		final int pInputs, qOutputs, nStates;

		pInputs = SpaceStateUtils.parserFieldInteger(inputs);
		qOutputs = SpaceStateUtils.parserFieldInteger(outputs);
		nStates = SpaceStateUtils.parserFieldInteger(stateVariables);
		return SpaceStateUtils.validateSpaceStateConstants(pInputs, qOutputs,
				nStates);
	}

	public static boolean isStateSpaceInputsChanged(final TextField stateVariables,
			final TextField inputs, final TextField outputs, final CheckBox checkStabilityClosedLoopSpaceState) {
		final SpaceState spaceStateExtracted = FileUtils
				.readFile(DSVerifierConstants.FILE_SS);
		final Integer nStates = Integer.parseInt(stateVariables.getText()
				.toString());
		final Integer nInputs = Integer.parseInt(inputs.getText().toString());
		final Integer nOutputs = Integer.parseInt(outputs.getText().toString());
		boolean isClosedLoop = false;
		
		if (! (spaceStateExtracted.getMatrixFeedback() != null) && checkStabilityClosedLoopSpaceState.isSelected()) {
			isClosedLoop = true;
		}
		if ((spaceStateExtracted.getMatrixFeedback() != null) && !checkStabilityClosedLoopSpaceState.isSelected()) {
			isClosedLoop = true;
		}

		return nStates != spaceStateExtracted.getnStates()
				|| nInputs != spaceStateExtracted.getnInputs()
				|| nOutputs != spaceStateExtracted.getnOutputs()
				|| isClosedLoop;
	}
	
	public static void setSpaceStateObject(
			final StringBuilder strSpaceStateValues,
			final SpaceState spaceStateObject) {
		final String spaceStateLine = strSpaceStateValues.toString();
		final String spaceStateModel[] = spaceStateLine.split("\n");
		
		spaceStateObject.setPrecisionBits(getPrecisionBit(spaceStateModel));
		spaceStateObject.setIntegerBits(getIntegerBit(spaceStateModel));
		spaceStateObject.setnStates(getStateValue(spaceStateModel));
		spaceStateObject.setnInputs(getInputValue(spaceStateModel));
		spaceStateObject.setnOutputs(getOutputValue(spaceStateModel));
		spaceStateObject.setMatrixA(spaceStateModel[4]);
		spaceStateObject.setMatrixB(spaceStateModel[5]);
		spaceStateObject.setMatrixC(spaceStateModel[6]);
		spaceStateObject.setMatrixD(spaceStateModel[7]);
		spaceStateObject.setInputs(spaceStateModel[8]);
		if (spaceStateModel.length == 10){
			spaceStateObject.setMatrixFeedback(spaceStateModel[9]);
		}
	}

	private static Integer getOutputValue(final String[] spaceStateModel) {
		Integer outputs;
		String[] temporary;
		if (spaceStateModel[3].length() > 1) {
			temporary = spaceStateModel[3].split(" ");
			outputs = Integer.parseInt(temporary[2].replace(";", ""));
		} else {
			outputs = Integer.parseInt(spaceStateModel[3]);
		}
		return outputs;
	}

	private static Integer getInputValue(final String[] spaceStateModel) {
		Integer inputs;
		String[] temporary;
		if (spaceStateModel[2].length() > 1) {
			temporary = spaceStateModel[2].split(" ");
			inputs = Integer.parseInt(temporary[2].replace(";", ""));
		} else {
			inputs = Integer.parseInt(spaceStateModel[2]);
		}
		return inputs;
	}

	private static Integer getStateValue(final String[] spaceStateModel) {
		Integer states;
		String[] temporary;
		if (spaceStateModel[1].length() > 1) {
			temporary = spaceStateModel[1].split(" ");
			states = Integer.parseInt(temporary[2].replace(";", ""));
		} else {
			states = Integer.parseInt(spaceStateModel[1]);
		}
		return states;
	}
	
	private static Integer getIntegerBit(final String[] spaceStateModel) {
		Integer bitInteger;
		String[] temporary;
		if (spaceStateModel[0].length() > 1) {
			temporary = spaceStateModel[0].split(",");
			bitInteger = Integer.parseInt(temporary[0].replace("implementation <", ""));
		} else {
			bitInteger = 0;
		}
		return bitInteger;
	}
	
	private static Integer getPrecisionBit(final String[] spaceStateModel) {
		Integer precisionInteger;
		String[] temporary;
		if (spaceStateModel[0].length() > 1) {
			temporary = spaceStateModel[0].split(",");
			precisionInteger = Integer.parseInt(temporary[1].replace(">", ""));
		} else {
			precisionInteger = 0;
		}
		return precisionInteger;
	}

}
