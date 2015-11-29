package br.edu.ufam.dsverifier.application;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.stage.Stage;
import br.edu.ufam.dsverifier.domain.Verification;
import br.edu.ufam.dsverifier.util.DSVerifierUtils;

public class ShowInputsDialogController extends Stage implements Initializable {

	@FXML
	private Label x0;
	
	@FXML
	private Label x1;
	
	@FXML
	private Label x2;
	
	@FXML
	private Label x3;
	
	@FXML
	private Label x4;
	
	@FXML
	private Label x5;
	
	@FXML
	private Label x6;
	
	@FXML
	private Label x7;
	
	@FXML
	private Label x8;
	
	@FXML
	private Label x9;
	
	private Verification verification;

	public ShowInputsDialogController(Verification verification) {
		this.verification = verification;	
		
		this.setTitle("Inputs for " + verification.getProperty().getName() + " Violation");
		FXMLLoader fxmlLoader = new FXMLLoader(getClass().getResource("inputs.fxml"));
		fxmlLoader.setController(this);
		try {
			setScene(new Scene((Parent) fxmlLoader.load()));
			setMaximized(false);
			setResizable(false);
			setAlwaysOnTop(true);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void initialize(URL location, ResourceBundle resources) {
		try {
			double[] inputs = DSVerifierUtils.getInstance().getArrayInputsFromVerification(verification);
			for(int i=0; i < inputs.length; i++){
				switch(i){
					case 0:
						x0.setText(String.valueOf(inputs[0]));
					break;
					case 1:
						x1.setText(String.valueOf(inputs[1]));
					break;
					case 2:
						x2.setText(String.valueOf(inputs[2]));
					break;
					case 3:
						x3.setText(String.valueOf(inputs[3]));
					break;
					case 4:
						x4.setText(String.valueOf(inputs[4]));
					break;
					case 5:
						x5.setText(String.valueOf(inputs[5]));
					break;
					case 6:
						x6.setText(String.valueOf(inputs[6]));
					break;
					case 7:
						x7.setText(String.valueOf(inputs[7]));
					break;
					case 8:
						x8.setText(String.valueOf(inputs[8]));
					break;
					case 9:
						x9.setText(String.valueOf(inputs[9]));
					break;
				}		
			}			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}