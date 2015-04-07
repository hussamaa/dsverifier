package br.edu.ufam.dsverifier.application;
	
import java.io.IOException;

import javafx.application.Application;
import javafx.event.EventHandler;
import javafx.fxml.FXMLLoader;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.stage.Stage;
import javafx.stage.WindowEvent;
import br.edu.ufam.dsverifier.util.DSVerifierUtils;

public class Main extends Application {
	
	public static Stage mainStage;
	
	@Override
	public void start(Stage stage) throws IOException {
        mainStage = stage;
		Parent root = FXMLLoader.load(getClass().getResource("principal_new.fxml"));	    
        Scene scene = new Scene(root, 1024, 600);    
        stage.setTitle("DSVerifier - Digital Systems Verifier");
        stage.setScene(scene);
        stage.setMaximized(false);
        stage.setFullScreen(false);
        stage.setResizable(false);
        stage.show();        
        stage.setOnCloseRequest(new EventHandler<WindowEvent>() {
            public void handle(WindowEvent we) {
            	PrincipalController.executorService.shutdown();
                DSVerifierUtils.getInstance().removeTemporaryFiles();                
            }
        });                       
	}
	
	public static void main(String[] args) {
		launch(args);
	}	
	
}