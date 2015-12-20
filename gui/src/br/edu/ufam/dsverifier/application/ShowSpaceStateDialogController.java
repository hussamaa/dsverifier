package br.edu.ufam.dsverifier.application;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TextArea;
import javafx.stage.Stage;
import br.edu.ufam.dsverifier.util.FileUtils;

public class ShowSpaceStateDialogController extends Stage implements
		Initializable {

	private String strBuilderSpaceState;
	private final int pInputs;
	private final int qOutputs;
	private final int nStates;

	@FXML
	private TextArea textArea;

	@FXML
	private Button btnReset;
	@FXML
	private Button btnSave;

	public ShowSpaceStateDialogController(final int pInputsVariables,
			final int qOutputsVariables, final int nStateVariables,
			final boolean isClosedLoop) {

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
	}

	@Override
	public void initialize(final URL location, final ResourceBundle resources) {

	}

	public void resetMatrix() {
		textArea.clear();
		textArea.setText("");
	}

	public void saveMatrix() throws IOException {
		final StringBuilder valuesMatrix = new StringBuilder();
		valuesMatrix.append(" \n");
		valuesMatrix.append(nStates + "\n");
		valuesMatrix.append(pInputs + "\n");
		valuesMatrix.append(qOutputs + "\n");
		valuesMatrix.append(textArea.getText().toString());

		strBuilderSpaceState = valuesMatrix.toString();

		FileUtils.createFile("file_temp.ss", strBuilderSpaceState);

		if (FileUtils.isFileExists("file.ss")) {
			FileUtils.deleteFile(new File("file.ss"));
		}

		this.close();
	}

}
