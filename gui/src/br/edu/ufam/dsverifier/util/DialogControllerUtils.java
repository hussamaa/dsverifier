package br.edu.ufam.dsverifier.util;

import java.io.FileNotFoundException;
import java.io.IOException;

import javafx.scene.control.Accordion;
import javafx.scene.control.Alert;
import javafx.scene.control.Alert.AlertType;
import javafx.scene.control.ButtonType;
import javafx.scene.control.TitledPane;

import org.controlsfx.dialog.Dialog;
import org.controlsfx.dialog.Dialogs;

import br.edu.ufam.dsverifier.application.ShowInputsDialogController;
import br.edu.ufam.dsverifier.application.ShowSpaceStateDialogController;
import br.edu.ufam.dsverifier.domain.Verification;

@SuppressWarnings("deprecation")
public class DialogControllerUtils {

	private static DialogControllerUtils instance;

	private DialogControllerUtils() {
	}

	public static DialogControllerUtils getInstance() {
		if (instance == null) {
			instance = new DialogControllerUtils();
		}
		return instance;
	}

	public static void showInputs(final Verification verification)
			throws FileNotFoundException, IOException {

		final ShowInputsDialogController showInputs = new ShowInputsDialogController(
				verification);
		showInputs.show();

	}

	public static void showAlertDialog(final String message) {

		final Alert alert = new Alert(AlertType.ERROR, message, ButtonType.OK);
		alert.setTitle("Warning!");
		alert.showAndWait();

		if (alert.getResult() == ButtonType.OK) {
			alert.close();
		}
	}

	public static void showDialogSpaceState(final int pInputs,
			final int qOutputs, final int nStates, final boolean isClosedLoop) {
		final ShowSpaceStateDialogController showSpaceStateDialog = new ShowSpaceStateDialogController(
				pInputs, qOutputs, nStates, isClosedLoop);
		showSpaceStateDialog.show();
	}

	public static void showDialogErrorStateConstantsValues(final Accordion accordionPane,
			final TitledPane[] titledPanes) {
		accordionPane.setExpandedPane(titledPanes[0]);
		Dialogs.create().lightweight()
				.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
				.message(DSVerifierConstants.MSG_ERROR_POSITIVE_VALUES)
				.showWarning();
	}

	public static void showDialogErrorMatrixChangedValues(final Accordion accordionPane,
			final TitledPane[] titledPanes) {
		accordionPane.setExpandedPane(titledPanes[0]);
		Dialogs.create().lightweight()
				.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
				.message(DSVerifierConstants.MSG_ERROR_MATRIX_CHANGED)
				.showWarning();
	}

	public static void showDialogErrorMatrixValues(final Accordion accordionPane,
			final TitledPane[] titledPanes) {
		accordionPane.setExpandedPane(titledPanes[0]);
		Dialogs.create().lightweight()
				.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
				.message(DSVerifierConstants.MSG_ERROR_MATRIX).showWarning();
	}

	public static void showDialogErrorInputValues(final Accordion accordionPane,
			final TitledPane[] titledPanes) {
		accordionPane.setExpandedPane(titledPanes[0]);
		Dialogs.create().lightweight()
				.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
				.message(DSVerifierConstants.MSG_ERROR_INFORM_VALUES)
				.showWarning();
	}
	
	public static void showDialogStartingVerification(final Accordion accordionPane,
			final TitledPane[] titledPanes){
		accordionPane.setExpandedPane(titledPanes[0]);
		Dialogs.create().lightweight()
				.styleClass(Dialog.STYLE_CLASS_UNDECORATED)
				.message("Space State is ready to be verified!").showWarning();
	}

}
