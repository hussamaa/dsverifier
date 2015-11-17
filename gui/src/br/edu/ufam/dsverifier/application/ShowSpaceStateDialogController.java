package br.edu.ufam.dsverifier.application;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.geometry.Insets;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.GridPane;
import javafx.stage.Stage;
import br.edu.ufam.dsverifier.util.FileUtils;
import br.edu.ufam.dsverifier.util.SpaceStateUtils;

public class ShowSpaceStateDialogController extends Stage implements Initializable {

	private static final int COLUMN_VECTOR_SIZE = 1;
	private String strBuilderSpaceState;
	private final int pInputs;
	private final int qOutputs;
	private final int nStates;

	@FXML
	private GridPane gridMatrixA;
	@FXML
	private GridPane gridMatrixB;
	@FXML
	private GridPane gridMatrixC;
	@FXML
	private GridPane gridMatrixD;
	@FXML
	private GridPane gridInputVector;
	@FXML
	private GridPane gridFeedback;
	@FXML
	private Button btnReset;
	@FXML
	private Button btnSave;
	
	private boolean isClosedLoop;

	public ShowSpaceStateDialogController(final int pInputsVariables,
			final int qOutputsVariables, final int nStateVariables, final boolean isClosedLoop) {

		this.setTitle("Setting Input, State and Constants Matrix");
		final FXMLLoader fxmlLoader = new FXMLLoader(getClass().getResource(
				"matrix.fxml"));
		fxmlLoader.setController(this);
		try {
			setScene(new Scene((Parent) fxmlLoader.load()));
			setMaximized(false);
			setResizable(false);
			setAlwaysOnTop(true);
			requestFocus();
			centerOnScreen();
			alwaysOnTopProperty();
		} catch (final IOException e) {
			e.printStackTrace();
		}

		this.pInputs = pInputsVariables;
		this.qOutputs = qOutputsVariables;
		this.nStates = nStateVariables;
		this.isClosedLoop = isClosedLoop;

		generateMatrix(gridMatrixA, nStates, nStates);
		generateMatrix(gridMatrixB, nStates, pInputs);
		generateMatrix(gridMatrixC, qOutputs, nStates);
		generateMatrix(gridMatrixD, qOutputs, pInputs);
		generateMatrix(gridInputVector, pInputs, COLUMN_VECTOR_SIZE);
	
		if(isClosedLoop){
			gridFeedback.setVisible(true);
			generateMatrix(gridFeedback, pInputs, nStateVariables);	
		}
	}

	@Override
	public void initialize(final URL location, final ResourceBundle resources) {

	}

	private void generateMatrix(final GridPane grid, final int numRows,
			final int numCols) {
		final TextField[][] gridField = new TextField[numRows][numCols];
		grid.setPadding(new Insets(5));
		grid.setGridLinesVisible(false);
		for (int i = 0; i < numRows; i++) {
			for (int j = 0; j < numCols; j++) {
				gridField[i][j] = new TextField("0.0");
				gridField[i][j].setPrefSize(50, 50);
				grid.add(gridField[i][j], j, i + 2);
			}
		}
	}

	public void resetMatrix() {
		resetValues(gridInputVector);
		resetValues(gridMatrixA);
		resetValues(gridMatrixB);
		resetValues(gridMatrixC);
		resetValues(gridMatrixD);
//		if (isClosedLoop) {
//			resetValues(gridFeedback);
//		}
	}

	public void resetValues(final GridPane grid) {
		for (final Node node : grid.getChildren()) {
			if (node instanceof TextField) {
				((TextField) node).setText("0.0");
			}
		}
	}

	public void saveMatrix() throws IOException {
		final StringBuilder valuesMatrix = new StringBuilder();
		valuesMatrix.append(" \n");
		valuesMatrix.append(nStates + "\n");
		valuesMatrix.append(pInputs + "\n");
		valuesMatrix.append(qOutputs + "\n");
		valuesMatrix.append("A = " + SpaceStateUtils.getValuesFromGrid(gridMatrixA, nStates, nStates));
		valuesMatrix.append("\n");
		valuesMatrix.append("B = " + SpaceStateUtils.getValuesFromGrid(gridMatrixB, nStates, pInputs));
		valuesMatrix.append("\n");
		valuesMatrix.append("C = " + SpaceStateUtils.getValuesFromGrid(gridMatrixC, qOutputs, nStates));
		valuesMatrix.append("\n");
		valuesMatrix.append("D = " + SpaceStateUtils.getValuesFromGrid(gridMatrixD, qOutputs, pInputs));
		valuesMatrix.append("\n");
		valuesMatrix.append("inputs = " + SpaceStateUtils.getValuesFromGrid(gridInputVector, pInputs, COLUMN_VECTOR_SIZE));
		
		if (isClosedLoop) {
			valuesMatrix.append("\n");
			valuesMatrix.append("K = " + SpaceStateUtils.getValuesFromGrid(gridFeedback, pInputs, nStates));
		}
		strBuilderSpaceState = valuesMatrix.toString();
		
		FileUtils.createFile("file_temp.ss", strBuilderSpaceState);
		
		if (FileUtils.isFileExists("file.ss")){
			FileUtils.deleteFile(new File("file.ss"));
		}
	
		this.close();
	}

	}
