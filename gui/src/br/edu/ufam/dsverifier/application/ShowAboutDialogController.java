package br.edu.ufam.dsverifier.application;

import java.io.IOException;
import java.net.URL;
import java.util.ResourceBundle;

import javafx.fxml.FXML;
import javafx.fxml.FXMLLoader;
import javafx.fxml.Initializable;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.stage.Stage;

public class ShowAboutDialogController extends Stage implements Initializable {

	@FXML
	private Button btnClose;

	public ShowAboutDialogController() {

		this.setTitle("About DS Verifier");
		final FXMLLoader fxmlLoader = new FXMLLoader(getClass().getResource(
				"about.fxml"));
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
	}

	@Override
	public void initialize(final URL location, final ResourceBundle resources) {

	}

	public void closeAbout() {
		this.close();
	}

}
